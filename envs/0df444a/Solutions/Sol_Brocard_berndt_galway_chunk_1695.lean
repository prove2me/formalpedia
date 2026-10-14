-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1695
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:20:25.352786+00:00
-- url     : https://prove2.me/submissions/38056728-1d2b-4223-9f29-0c7285b30dbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 304676258 ≤ n < 304856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 304677508 1250 304676258 304676293
    0xc0506130305100902030708010911010503041a010e1806010506030612160909140102031b0a02010e010f0204030611070f030f0509180a0b010311030f06010519030c09061103030f09 79
    0x1112103003e400029000600c1c8149070411700705038031002050b45400e1010b80070901120424000010900e48266203903501d14010321000b100c410b144100c40d00400000c0703116180c0b040220b006400780c10086c0c400014000101c6d60b01c03075090103aa03802c45400d0000c19091709001d0840342c0e880740107006540b1b03280525420301400c00401d6114880e00d1380ca400207242030000d140320f2104202070b0140203514610342806807000313580e401b520901c0a078900107411811035200398000400b201180303000344101c10b644041c40019400c40d00082d104146007440205401c1c03142411203180550100140e06204060307107080c0ca0f04c400441d603a80500c0f5041000440f556100c20a0701c4200e0700e1401c5034002c6044ca4547c02003200d18114200303041c54036000e24401071400c3c3c40c050340c0e48401c110f03a24186136a12500129014060240b0040c2c0000017801020b04003a0190070114000005948900e00302c0d07a00e403003c03608000d007560284e0143d0010000300c2c1c2080d40c00e07074001d030b408045401240c0411004006114 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 304678758 1250 304677508 304677523
    0xf070c0509040b0402101403040201110c18010906120308191404032705010e040906090605100e160807030b0f06033d060f14340c0506130305 62
    0xc54000000041008518046d40d803070491900070702c4c024171a5040c0c4e50a410003032001403c00381c14803940d1500561122003c1042038070480019002502c40390b1082c41100f803140083c0a01c2940710b08200e0003140c0c800c081d1212140194241d07491040365100c6101d444621425490200c076240d407549580d040303915083c1007650183e442603a41028002003060560f601301089150002c007400002010407003680e014524400d600000c8600103070009030707451315800070910402d00410250a1a081000e40d040040520302110b0b104081c85649540b04401049100340d800c0b800030119030701d040071407070302d500c2607014030709182d0003600f5140e15882a070005280c6400440745000c0041075510031008015a00121501540310528040c0200048400c2400c410300e40340900c404105e1280c6d40100c020784103001841ca407001c0d00b0441995034546c0d03400246c10344c0c0385003000b5030f011102d1103010b04120260181074484a070001ca08803e401e040404211080d841403926010340c00610001102280e418413071f09 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 304680008 1250 304678758 304678763
    0x10203130213060602071703040e070f020d05070b010911070215130f050a0e060a120b060a0b030603060703110c0321060303040303081512100b010e150f070c050904 72
    0x80d103035000c60320411108a50104801081034140315003081030980016041c016078a1400100ca41e035082511014a5401684d00c102410b11012040c0a0215046074908100d8101d0707900b90f64005d0682c4505854a120385070001300075071000d500400010400e0744c8400480c8031090b515515100007034000516185010030f66100d0085c4c0081e038402c0c40603652203e40010813100c1480050035140c000002c21403071540c80344411003000240010181e50366100301201808030540e01840c1e000c4d060034010880d46048400314040e030321240e000302e4000025800c1e2881424010300816556903041d200700c011740144a0488000e001c00d002c0c01c002d80324240040d0882303603000c80c051140c0f4040c4040344516a84050900c80c00b0350810070051000c20750080200780c0c000a00c0b250f0040003142a00407640c500c0042003040d00310300501203d038508843e1034204081d903071403da90ba54a5907040d4402c00441100e01c401004081321b04000c000c0182c1d6809010f40601805210700d495032035a100d02280705280c084908 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 304681258 1250 304680008 304680031
    0x12010c0806030c1e06030a090b0115020c0603090c0d0c050607210e01020d0e190e0f0a06051318080a02030406020f070e01061209080d091709030a021c0203010203 71
    0xc01c845800d080011283c9140c0482d20300c00720320740444030340b02100324420080740500e1001002803c1360310f168008000155000b0018081980e4600c5403101101c0d41a10039401405051020050f92400304240c9000303000c0c08000d800d0f01c005c2103003000b11000140d0412280040300c8600060300703030b0f0f44401511106000742603480103d100400303040d668515001c001c60070b03c00c1c1071040c41d009990000307441300d03049080d0a208001d4920400050142003d04040c1e1600d41d0f605a8046240304100c850b45003d210b4000492481c3e8941020403015260140a40b41c8c100c411900c4c21100d03041a900b240d048a101c45000c0d0380300c4100e6450710407080c1c0c4003c4842004d6400010108242035041150f03404407074201c000380ca20f0b80e080400d0040b070040184900c104004401c0c80240180f5034560100c030000354420311095407205c8520103d80a002e43c104c0c151418240341c824403405078400b008440070b0400080107000c0d106299800c00613505030404000f90114840900b420050b2000d100031801104500107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 304682508 1250 304681258 304681261
    0x20c040213170109081e04211202150a020d0615020703050709060f05121504050705031504051005071218020901050d231501030804050a0608010e07050912010c08 71
    0x718044002c00340c4651a81c42d82c0f5002c2c2c040041452030094902c850088100071052440360700c1501d4150080350400984404c0541d1407880d4900203404030030b0300c241301703024001545524030000e0f620391015016100318913417000001001070300103500030189459901000140c2c1901d0750b0082441d0080c1002400c09030340010024030600038100300c008000c00d614001404400d082014688100505102d12806401e4100c00d8280140341800040f540c1c4c20a501c50204510b01810965541e42203841143d00034000d010301c41a000c20205c01551007190418000d01c002c000060480e802408000c022034104100e07121203601c440c03403034021105400d0300000c000200754400d0040284a400680c4160702c662a10502c44c1d001030a0403c405e09507000100f00d181429014914141c14a1510720003550340c52101c0c4004001c0001c0c40010f401660701c144d400103c2c0c56214101640c0c1070380203010700300243c183c4100181450740319400401c01068050a83c28822025415807820758002450320804030b400e200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 304683758 1250 304682508 304682519
    0x6090106050307080a021507080c010b01030605062107021207030f02060c160b062202030a0b040510031212021902121603200706180f0e010510020c040213 68
    0xe0040640001c40c0a0400c5500d020381160f83d030480c003000203015a002c04520400318a6080aa545080d0072809050341d405501c101540200344182e06a800f0910b08007006c035650400c0741c155120f1074070f04281d20a2a880186800c5140d8000600d02000c41c85200f258003c004650005025958440e440d80e0403544a4400043d085c10030042255820440038031403c0d0407081204c28420700503801001810705500c0c2c20303000c100581c010341c00d400c205c1c009106410500010340d5000350300c078414000041028881000c20001038620076107205441c020000310074008118200c140c031040030940d08010000074203c1001c002a03800641e12825402289030116506507014041150b18100d444031891502d103c031900482015030f585005810041990390300e12900300e01c00305c0d8800c010031410031140c101c0c0c1d0340c1c4401400701c810f028548801d03091031800000c001a900019205480e001c01c50154180c0c04c05040c40311224501d03180a0442c450b60303036603070342070785452001b0400803003c50a1040c00741e0810 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 304685008 1250 304683758 304683761
    0x270601080d1b0b100305010c02030702090c041a0a0e10091e150c050102070b090d090b030615090f0406030c0f0602030f0901050901121503060b121b01030617060901 72
    0xc07030400d400e1000411030304400580c40b4038034081e181e0348020396203d44d8480200034000442c40d0f40005203150300e0300807054100c1d0740000203020040e10071a14113001c1d40e41d54221880c28001c51203007181282c09840341094400d0030001400c0001640e25140c4170881030034000441891014030a400450503100040c460b40417090780401c2c207040d68800c100d0803185013100049920408004501c2041041282030040000a4045828198028001781c2941c01c284040b00e40326214528420040341107075400240c0150034005a920a0700300801c201c403101c521140e940030a80c0310450301c44e4046507124080c081c0d9a07a520a80c8003a502030b074007821a190419a4007440c0380700c980c2001040d9131040c01100c07c1800000125070141c1002c0c80d00e151101600b0300140e54007076111003071502a50130b0801181d000c4540030344a0045038040e00040c01900b0046041c080e40d80306440c1003c00315000310004064641d849054101e6035501032600052069503000c550008507130380c50030919160482c5c014080c51803400d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 304686258 1250 304685008 304685023
    0x18130606090c030f090f021009030602040e0f06100909090c030f060605090631021c020703030c210e19081209070e0103030f020327041413020927060108 67
    0x400004205c094aa178503041041608060b000340315400102c81d4074103851040202d14021640b048096484684840421298220840d03c54454151850029103149030800f180b061292240e110114030703a09003002e50000d860182020b40c1c1c1c484000c103002000810030900c1a11544c01842c0000f01d01c0c0c02e010401100c503002034200c80c81030250f0036400540c0490042c03070031034084544061890f14882c1a480102a000381d03920444030b4015050110340c070550740c1d00100809442990200100342c0c05590a54150410940c0d82c440803601c180440a10142580400c4a40c1801000c6824241d14540082c8911024002c01c03a940b510100b0302c0c800142280842c5a0444601405025000c0c1003a40b1081070110504c40501040f60002e00f410f2158000e00880d00310340072480e200030180411030000400301a4140c01d20340181d180c05000c00b00b041000055034048c030384207698201d900116800300844010b010300034180c1d000d0f002c840e03c040c461046000000120351500505140d41c9030100d842e080c044da = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 304687508 1250 304686258 304686281
    0x33090607081c0537141608010506070c0902091219150209030616030b0d0b0414060610030906062310050906090409051e060a0605010e18130606090c03 66
    0x355907003504100f13200b50720600540e141003e4006103507046203014002400c40388110309100400881030041001c00d01c3c14001c159201600c400d20075907650b03030610113644501580940941111801400080c134250024040c41d0707030003440414044c08045900d41070803038a40655203071114142564040040b043ca85000305d03104403000314148034040002c01c0d02e40c031000b0801003801407015800c462150080e0b11041c0c038031170060b10300c0b680070b4242d00c1c0001107450141d4050710204003800780807160841c006909442050090419504001c07408000e0300601010501200c046880c1c00011581c01901051945507402c20317a6584190f500300000e000c60410041e018600300402040f540d515620b407034088075100d1a041d940014012040d04080341000c045030080c4400d40040b000402448a000500030f008410800007000071031f03511001550031800040b5219081049866100303441e81e008031419500a60001c0d082084140603501c8070119620380c0c202000095546001d00d20060b81441582c004c48c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 304688758 1250 304687508 304687531
    0x7141605040e0c041d0307051f02030601020705220219031d06370903110d090b03100e0c071a01061b0212031833090607081c05 56
    0x25002e00464540d28025001c6029070303141c82000c4121084090305504c102d03485002d807a140c05003450400d0310b07040c1c100c80c034646410340380c280010903040b180300312401000c0503001004003a240c01c05122005050010310002c1600c200403650840c06140000c0c54104244d0400d009a440100d078054229624481d920036800014992100c0000d4001403041c0c11035071505684030b4550054042d03504015100c4598420050840c2d0804504842a04010b032041c0c400c2e00c2e02822041c801a04940d034003c080b81500004038203420802c40443e9280c000c41c2c009504019001c1c45075140c101340d00c80c440c0d058648090b0260001007540503c50321000c421a03c41000c0c102c0f01042d49440d50080441d56420908246007141035008400c40d41c455071001d641407000020b803034450b001e1035001c030702207408680b101d07001b00800040740001000b00c03007640c07210000c00060040c6d03001d5029401199500184074070394022804100741004200042d024020610048414412400311182c8500c2541c00c050043c6510343d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 304690008 1250 304688758 304688771
    0x4090504051207050d0503060f130b0405010503030a09031e0512030717010f06050c070e070e1e0d0f05070f0b0a020c220c090e01030b0f130305030115050714160504 72
    0x1074001700fa40182801e191074015241e031a0500000c1c0200c2c01e44a142da800386803e21340c4006000260004401840c1c120b5042013035070390364030502da1a0300c1000d0003000020300000d0f0600004a201c54851183c032408049001c00300c0306541c42500d00806030030030488011020040040305030384003071001240200c240036075a095161900d42c038030a151a01501c000d200c80820402002c00081264000a02090f01ea2305c845003440c3d01c001e0007071074241180c60302400106103807031070800085d0f154001a550103000800703400c2c0c494030b500400b1010880e003100d4500a03e080001c00541d03040100000d0010200c00a5403260300d90340103850308070250401d50003200408582000800e0518603103001c00c0040c030b40851600c004040c11544811550014031100b010080080180413000703006610818400c0e0202180b51110700c03802c1d1340012421401400148100010b108114a02c81d094411f20280d081c141e0070a402507031080f940c04d1210b0141c140a5020000d80781a9100b0507003940000c0000350307030801a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 304691258 1250 304690008 304690013
    0xb040e09030a1409030a060c090915050a05011809020a031512051c03020408120712022a04020903060a0b090105010c0203030d0203060604080a03080601021018031d0604090504051207 80
    0x2450f6103001100180404110720400b03480900c03420324a583d0100040100d0080020081d0035002c89000d000d110320b240520640e24840b00a030001d054400c000d000b20b40607450b1100440d03142150100c1c41c0201c03031401300d0006c0c0c11480c034005818260b4241d28045240c00d00c0e6220401c80105941c480482500c41c40c4845001c50300200350344000c885044200146811102029000f80c03090354001002c0d07115541344101030707000b4074014003207c0340700308258140f00256810403a5146280040410a801c00100e110345140c65140f4200b03a107403000d0009070030010b001d40021304000c1e08880ca5010b064403490012824a4070801c0c3c00e016280074200f000310324102da00443d9a90051040c607031100e680c00000b0808654400065400800c10642100d05e40c41051030300403c0200f00750748141c0035204010842120001d14000c09604003d801c101512074001901d040702d11460554140c02210824000880b0940301c68004001406205070082000d081520f0100e01d00705542c00b00c0a0811001c0c880e0000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 304692508 1250 304691258 304691267
    0x10507030f09051206040606060509010212131a0d0f0203010b070b090f0a08130608040206070f1a1f0801050601082a070b151008220203070b040e09030a 67
    0x104a50549031034010100c00050584004000d0b80181d07034484082e080110310000d00082d80c0340f00798032540c0e051000036582c940c10b0307031135024241d41c440c003580200c503140c10350a803288040c04000400702c40850fa055541c21151018400c600205903001000080c40304084070180540700c09806140c00451640d0315025880c0140e005244e00141160b43e0381d00404c50214040162403800e0480390142c90446982c0e02d44140d00d03520008200d400c03405a45000182140550000723442641c011345034514215855548411025410508807494042c840f072142410140e1000d05200d142c4240200f05e9203d01c461042d08c6e130f81415400022181c1c1050100041c50740d1203081c1c075800c402c040c1034800c1c2030000c0e20801c7c522181c407600071210052000c250756050280480005000d43c482c0424640c1000d4160140b050506c030000c0320724081801103001c60903614113828041c0031f4070303034801642c010008240d00103070800c4500c1d0b104000d60040810284090000540540c0d0081d00f404001d524003503d0210160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 304693758 1250 304692508 304692517
    0x52a010e0a05010219020301020c0706021c020a020a030204020f1201062601031a090f01020c0a030305062e1b200901030c0308090f090403170c0c100f090b100e0a0b0105 74
    0x1000500880d05c07004544094041c0c0f0014031880c002d40700c020f910b54030025038a07924425a416070a101100d0668000e002058864009402502843e1103a01f0364013070101a41c090a0b440425660400c92030810240c041c61183c00380490303554075401c08203084c801d0240290f6030341140798882c262200400006002e0540f00302010302d40741d84c4211540d01d03a68039508011582e40c08500d5540005900c201c0e104020a031058464800e403401c20494840c4814056081807240041d802104024036403c5007191262641031990035a14155409a00507480341000b0a1003120451712440e04462681d001821000d5040c40c9120036103104070305600d90740301c1e10100055440090100c3c00c00245105060321801d542c013004510181044006040c280f40c01800d40381402007001a100101e00815100203c3c5000c81e20182c2c5644000c0c6a811551562a030080c450f680048940390f964042d0040002c1e82181824440c07501044d0340320079145080895404900d00615a404071362a040c00c078401681c0100513076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 304695008 1250 304693758 304693783
    0xb01020a0f020303120f250c02010c02190b0301090f09051b0307050603130506010611032a0a1202010501060203040b0a0c03032406021506030a0f052a010e0a050102 72
    0x14240307520745002107820f40c0714000c1088101004507080142030707045690264014800088400055085054000e09088003110400005a9243d0b820f0b0095031040d0411000203000400b81d00b040521940030614080c2c0b260b20401501c00041700404c002d40c128800c00c1081c0100e500300f4407900445550703007500c130f489450805841000c1802010080d840820014002e804003030b0649a69043c401740d40d1151201d080381c1210a072081c1e000204680e07104d2000d002c4040340d0324006505002c1522020703040317400c101d0400b4a4202500485002e1a4001c111154540d405081c1d140c804c682100002070964205800c034005542c006c100420a501005040f500e03030417614071744009144140d2500f1000307003244100c1921540001c0e5016801d1508442e03e40e0308884407034003202c000b036550b42601d126511080790040e40c543c112510707010120b03d03510310849402e0312038029240d00140381c0d101010b540c00d044454000c07c0d0a10049101c0d10358000e0a98852180110b55500c840b614002c0001e5036800480c041 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 304696258 1250 304695008 304695023
    0x3060807060906180f0609080c030115121a040b100623030603100c08011805100e0601110a0318050d2006070b040b040215030c16030e04090311010e010b01020a 70
    0xf01c0e108907040c40d810010740811176a580e030641d9580b6004002d441140a210aa0300072414190510328051040a030300604290f0030182c1c1e10314016a100b2105074180007510380708240c00c650104650242d000b01c1c451880780c402044e6030f0904e0102c000d500400398010405120326010000b8000010000380c82d420400070400c9983c070703510321021900380740041d018542c401d42018008100c0d260070080c903038181c8158840c7d03d144040100c0c018001c5d20b5094941e16100075002005120784407145a02551080044c1003240000c6c9100b40041d2411080290a400043e0001c11222218105e2101c0000600c01100e0002c1c80c00750344d449a80c0c58664265144074034003d03003c20701a2036180d13003042c0c44a00d500070000b03584518180c144818003050460301288206108203c5003141800482074a0154549c03443c403608040121101000d81c11000c00183c0c103004040720b0001581d5501d000e542a0b0500c207541c1d152280c0c0c101c0c00d420f425200403160704a416414038104855603680000c10149a40d0000d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 304697508 1250 304696258 304696277
    0x906090b0907050d090f050d08090f03040b0f030a140c0909010e040b06040b1c030509031207080f180637140f0705070609060e090f01060e0307170d03060807060906 72
    0x411301c250901b0010001d00e40c0c002d00030503203e600d800000d954071484000e0f058a109034007012105480f44035074020580785c810300380a00c007003880f8860080c65000c54035020010300b960307044e42d030504040d20448080c0000d03000040c0041c4141407007090780d401060035254152807814143e8035003800f0754004003140c0c0103a0b81c0b60030b0f505055468120403490091400c01c83e000350901c174100100a40c3c44030741c038203000784901d140320394000150800b00d8103807a400c6841103080000300d0b00111032540c094002c19240c0c8445070703d03100340c42e505d040c01001c041000140300005d2084d0b1024010541c90400e80941048407100501c402d242c0d004002c0c5400164042400ca0307590125003a0007481c2e0140b0400980349228103907021030466089442d0703800b51041c0d511515442e42c94030301003241c404421200b45002e035a801c401008058003508088a8030800142a03030007903a19520b5100c220120111002d149601c10700c0400c060303540600c240c10180c229400540710442c03c0c01c1010309032a869109040402c01c0d60030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 304698758 1250 304697508 304697513
    0x2604030c0f0605031b070f02100c0506100b0a05300a05100305060a0f0e010f0903110303011503091109040302161e050d020a03240515090a0b041103010906090b0907050d09 75
    0x140c40860182d4000c04009d03410440480c005e0540400080c1181e042c0303c1c10012561080706101d84000b203034181c401c2146080b1078100c00319541e4120180040c0543c41d407000c1c6c441e00d01400598880d9a400705490200c0c603142091a402c00c0c1c6002800540c4000404502407000c600701103403183d449041c2400115148004104180003805410f4101d8515407801d4421680b0104a81100c600140641d46805501c80d40350941502c2c0e100a12800c0300f0b4560040403004010700a0f0042600140076003641c46001149030045001c0440c1103604900580042c500320410016000012001e4111301042000c451001c040380d00c0d06100360f01566101e10210002103045688500d0000e0146900c0b0b50605140c0c403510341a0850108194043d92983d82450005600103800d0503461403040b01c002c07ca2009070311054000d50040c0710744040a50002d8840196442854a5400845c002c149541c03001805900c0c0c415241c080780c907401c242324805c02c40c5000f80b00086900000b0b5441084900c40d00240442203072 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 304700008 1250 304698758 304698773
    0x30c1413030b040503030105030c010f0801210b0702070e0109090f0206030414070608010e060409350a050309010f02070803010308180405010b03040b09010506010c2604030c0f0605031b07 82
    0x1c0c0e1006200c010711100304000c00c98040003540c106c4100740c0848100e416890019142a0390824040002442401c010490410407a03024081c000380408910740300c0c2e0045c1c461303c03c180d40480d54103025074443c003002c0002c1d8594041c02c0d4014003100700304010320f005554030200d030401d0b0542c1c040d114540c04000325081c0b080000c00724a4070358441c0c003100d81c419650400070b81500800d10400102c0c90a0a0028807182050b0064032840c0d54003402d02a0004095210140e00080029000082101c01071040101c0303055040203141d140d407151070305a202c0c0f0303103584010300791105a4a00003205005200000000d030114060340e040d00d41c00085640c6480c0c112982c81242d905854446602605100c0001240941040214007840c01100310100c15030f2207403e00c4d42668400c2d2030090000307000340a0394004c949841440807036a001405400601c400d0910342034051b81040d0801d5031880c000e103000300840940e4940c8100100030509201d41140360104c40010750003014069078031000400540301c2c0400011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 304701258 1250 304700008 304700047
    0x1a030c040b0a0c0b060114030604020d0b040612021507050d050c1510030209060306010f1406070605010f0612050705180102030d2a05040e070e0d0c060302030a0b01030c14 75
    0x44076034a40e2200c4416100600440300880180d91102140010800c25481600661124080c8141441c9151146014840294082c81d644480c840e501c2c8901d0400da43c5a00840c402450203c100011070f68a500401c80c14100c2c0c1d4840c02440001009510300213040171030313006241e42d680c0c02c0c01d6454559560881d82802424800002008419000c20108600d500c500384240d90007602c00c070103942c2d511414187c1d140030130700882d10081c9a001003000050366000d008540e8007406800c0c1410101035070f03502c03001d40740281c0122030540c207071810a00c55140d2091559807580742010b801e0003e13040004028185109840350340e84a0514848500d682d80d0080080340c0075840911010050b0b90326445c03003c60b1a01e90901c4820f06c100240c1e17404031280e80b2400558081e1341c60429114010780322454156440d581210400da007000340303140400302061129040744002c107841d480140c0d03245000c0081104881900c90700e503060501c1e01c00c10030021940180365100d101c03022080300e90390710803071286030313007680003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 304702508 1250 304701258 304701269
    0x7050708010f0c0c1a0a06030204050c03040b22330519091e0c0b0a05190c030203030402040e100c02011a0105031317070f050a03020d091a030c04 64
    0x61510000c0d91800550004480c00d010082c10086003610850450b402c07140e290340902403402c8054400900b110400700985c000c0380948002030851b0b030300e42c08507055032811514981050004000c000a20400078941e41d48010702d961050021042480c2c000019400064094003a0000c203460070701d940c90a20f1a000c00c0e201c08056000c05211030784117580549411941103c45840c0d45039007c5960500d07015540100b54040a105c00000091640c10680040c100060306c2e01e40c10341100080d6038100a00a1401d00f0b5241d075100d6a0b18100c5143d800000000c0c0d030450100000c100040d0b0101c0c1c0d000c4282e0b40c0042d4101c0b00850000034110000346418044a2030880709843c14010b8614583c0551041905020400414070152004401901c0c1400100c41c80c49244580d01c242000050ba120400c0c12145c981041d02400d03c42b06445050b4200c1100004503015401440315409141e010000c0210283c2d262400c0b02025080c040101c01c580002e0381161030025001c0040352030250348000782ca001c3c1c0f4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 304703758 1250 304702508 304702513
    0x203060616120f02071a03090102070c0303080a060b0702010c0204020319051806090c03070b0c10020f030f060904030516230102040e070302030709151b1407060810120201050705 78
    0x782d00b00a14500100718889010501c1e1042840c0c105002140300340032240701181503ea0140c1e84a0100f030700740d0000700604200d5500300308040c002164121480042e40c02035a07020401d1518000810440e01540c018a132800c006004c0c000050b03a0000b9034071411036051320056266203405c400c03a041d00c0c000c44202481d0504080c00c00c0400e580e2407019040b890303508011503413103072a09600c0e541c0324400300030002d4144e01704004c18060041c44900a200100790001201c182992500313002c4100e8122070103214004100005109400303811455070b0707400c54001c07150b001042c1066500903000e07114800c0301040003404a0a0b910501403400c00d5203586002c503040c000d06895140700315a00070751050107501d650300390070030214060a03c01c3c401e592046415456004050307092003105410500300c00440d104200d0b8902000c204210a091801509441000e1007000340c6c8180e44500c1c10301c120b641114042000e02c0c020000b0b1003000890030001c98401050785011803483e8001240e082c03088070f40150040c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 304705008 1250 304703758 304703797
    0x1b021e0904080a020d030501081c2a12180302040e0106180c030c0c110402130803070f06050108032d09090f090c0907080a050a0b030a05011407080903040902030606 72
    0x4420303402401440d20a90aa070180036010500390102d41f8280100da0550f030014401c100583c140b1441e40e24246454101880c1d414108000820381c003404042c4510001e48817407690007000000485c3c5074040040b8244188d1420604281e5209005d10740700203031140c0c1d145c481100311103200f035210601600500e08005022003410070340c10f0150071071144240000e03141420210183d03114000c200e10a41c0d001940300704124500c4100006500140d80c1952210481c0b5070004800c2e000b0802031890510600001004004508140c41180d00590080f030994201b04003050412200440252882001030660f9804440003240340d03840e40940825550094030001c00d1107400c2603103000185c071074030844040701e121595402c240040c04a09a0307031000450440008541058401d0b00800d62112401d0303400a028406800001d16010503840c1c02d9403240d41d10a44c000300c1800398031115034081c00c141060740240c28644185652440359101d640314155000c004a0300c187c0d200001c0316080d9004050340b6009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 304706258 1250 304705008 304705013
    0xc1509080304140118120e0a080d090e0108120f090306010612060902071e17041805090f07150c022214040510090203100218101b021e0904 61
    0x2035078030a4400b030703a1803003101c400c00346220414003580070814001120030740d688460b0b03640d03000050f0a0100e06818400c0944030810310381c0369480c084000700701c100f00400080b960b2135070142c4000e115801c22104404001d0060000a000203200020f82c1c00140015a4510600c0c0001d00580100c020907a4140200710000414540c48071043c00030303480050041020703558620201742203204401000f08130440c200c0c01d000403107005242041c24903004542401404102140c1d0704196403080c4c0220180390030f150036180d55070324244100d590041c0c040340141151508204803030344d200410302c1124a42840000401c90300b501c00e2202107481680a892440380c0d64410150748e1082c48481c0b1081100351901021740308084141c001c441c05503811174090030311030100500e1100508113130041680c00d807041000c800c02d03181c3d05100400340c400c1c4108c00c00120180c80e608000003400603007800410000c19058442100d0fa1030035402409550459103002d0b408000c42c1e140541d040402c801680c00302c4103004000a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 304707508 1250 304706258 304706273
    0x1504030c0f05100305040c05120c13020a030b09040c092c01020d18020f12030c0f07050f03120a0f14120f1003080403020409030c0804030c0e0115050a0c1509 69
    0x2030302c00c201c40982caa00b200180840c11503000b140c014000070f1040b1000c00036801e062035586c1420007000e003500d5003082410080741c4000480d400900506074006021203440d68940f0904075800f5003180d0346002070900c0c1d141c010766291180601c1004947d2002507480c00100c07038120042500008580320003020904403014000c3d0402d07121600d4403404e08900d010100700d4280c80d500115802400c103003414030071105101001c004038913100000d04c0304108980401c503003000581c1c0b690f28001c0041c01007509040502024035040340001e07000760700c05021003000800400c180d800b124002d2520441030308680e0303005c07142d01c02c90700c144080c5041c0c0080c0b00c1c070b8108450040d26102d102106199072003a216089084070b80300c0e6901c009491000240014801441d045c0c10043c1d5250007440c0c112450291502c6901041d40950300440d42d9210341d1100700b00c03100290944600624003500048402e0319195000740152054040315402c20001614150401803d40c0c1e264a40603040da1080207420314a161030803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 304708758 1250 304707508 304707539
    0x1504151b0903050601090209030a030e0102160906081e03030403050d0b0607060c0905030303060a09050a0906060e0702010b10050403020f180c0d29010f110303190b0307141504030c 79
    0x700d0f180154400460402643d00849125040c0a40140510320303c507203003281c6c407450480b4002d0450040a03030000041920a05800117050940340000b046413030017121a113004070500441c220581848d403074022860740802035a900a41505000e681c0c0d5840544406c0203107158082030740c0c4081d000c40c0040c03d10915900491204210b91104c1442da500c0700700b01031b138a000444032103038803041c48141808045d0003500036a41041c03100c000400d00180c0e40ea680e40640c5c603a504140440c1041004010800754240114510f05000743c2c0c50800741401000018444d211303e0101034080d81c0a400e1418090f05c0f01c81598050080e40404503005007400080b0084592101044541241c2012019461114200d51461285d4680038502c0c551803070240064646120407400d041c1402002d05202907031318030a20046120351095050154841d00c0c10b00303003004454610711b0090003603026841c148214105182000c1c40c0880846800e00701494241c40d141c1d1500c56a00000c090380c20b940340006103071401c201c520 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 304710008 1250 304708758 304708763
    0x7110d12080906040b0721020309010e060c0304030c020d030e150318060105030616090b2d12040204111308010911010f02120702060405120d111504151b0903 69
    0x141e40c540712540300316510581542c0c0500080e0309280803964042c0103928061716004240880107102da001d00408089030402c80d0b0b18840c50351280050910200c00740091a0720080404009042d420b09480c001c202004007030000f409000201c0c1d121003498081e10711601e04d420001c1c860000c3c0400c840300340c07410750001d0f55500036220540ca280707403440b1004202c503030586d1703405801001c04d6616012181c0900380707001c03031000c14804a5080400d0182109000f003200042c1c104000d0600e00c2d9200001c01d03400c1c0101c01905040006000344030001c0c0b03554002d43d820640494000c00c0c6041c00d82c04d4400e01d4401e9100c0c0c0100c00c000200d0001d10701030103400c9000c3e094017885404804611400054566035003403110440141c200c00b80880c542c2101c5809000742e10b0010300340c941090380f1140404c0c032400c00d0b0100d4891561080c108540071907813107103600c40d44210f0600a4456801511490034941e10040e0008244421610340054801500e501c04501c0503032100da00a8203001c00600607120703c140b07000a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 304711258 1250 304710008 304710017
    0x501170f041518262701110f030406020601120312150512011a1207031e080c0102091003020c0c0609040f060e1f0e061c0c33050301030807110d12 64
    0x3541c048911344403d68610b5122500c00e60348030000702d03e17459102540c0815103030500c007881c42d210002c16030410208950040c8003004599036420004041e241a5059010714000390040c031040c40041d6214806001d030300c05000740418482040301c83c60b404a0b0180d01700582041079501c0400326944150042040c1a12101c4181c44810018050000004072140b0219440d0700821081001850120104440010203c80d900201c81d203a5509903803503110342c244580581d00860700c80710794030704000803845000d22403d04624040c2e105000540f80d8100c602464441e0102194040158a407500241c0c0700c1c130540c910400889482d1405150364a00691320201c00d541e00705a40c800960740700d5809010b403048264200c4869492404000032451440d680c81c8030603565116540000b4411100c6402515001d03034032207050000010340090210030721024030a0641250720503460140c01c2401c5905407508100d025035074109500b00000034082c85010b003a0003421104614003808881c0b0410300980c01603658 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 304712508 1250 304711258 304711313
    0x1d0106091505090f070908010533130c02010216050d0f03060f0306050a09050a0506012108090103020c030c0703030e01110a0201120e0708010e06010501170f041518 72
    0x84155106070103903a801402d0700c030101e107141e0300113a40b09520140b90b18001ca07929460366240c5003954019640c40380b10a292070701d443c4401105418032080c82a01c2400d1100a080050002b05060000a8078186079030b40c5001c0b072000b0600c00c0d011620301004901c14044200e4081c034103142d07510004804500040d0303140d00a145424424091442140c5001003414019400c50310f44600511000e0b15035000b10356545013050018009100c0c40c2d10160090001d000258540848050080038030b095145850b0048414800010180419a18822001c1c40c0041c0c9034401070208a02d58802c0c411040054840c1d00d00001c10182d00120a10007440203030784050b848004090455558002c800d0000c0c00708520400060f030000c0317980d02c0282c8103000e2000f1a060b05940b14502801c5880408004281c1e40110b40103020950708865101c40305412028101c0c214908905844021341015000800042f810b0400340c4400595400041012410602202c82c1c0c890310319050700d040003203449a03410150600ea = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 304713758 1250 304712508 304712531
    0x8090a020325050d0c05011d0909100c0201021201030b041a01080c043903110a021b01020a050628050f0402120601080c010c0804030506010b130503011a12011d010609 73
    0x10302d03420400e80c8036074400000e80c00c00f401503c84800c1a230314207103045407008030446144e44800b0624080d080d124054102112a01a400b0030768661714951815a801000028162200210b0441c1143d400244d0000c0d286c9891821a1100d07038000c11804e400305040e0004280d801001c54150341e154011a01009046944040c0c00c002850b241480c2c895500c0098203e17106045c084040ba004100d0b910700000c1c00d240c1f41100302d0507600103246400040c1e01107403a51a4000805050400840b402d0000300499111550f445a48203070043c99100344509042603812003200b017141c140402980203000b0720030780c42c10440701c0342150002c48003a4400c60342c10640c0b41c0b13495000711320181a106084050b028002c01c00005449003010f1060032640802c041000101041c0c060001d18080c05005403065665404260703c148280d02c03c0e0031440c445c2e40351403ca00c0000f0328207203582501410540c1c0c1030800ca003084401a00400580e0134050b0350130007101c0d10084c032250661002042e1035070940200000c60584 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 304715008 1250 304713758 304713769
    0x70809030f031b0607091403010b04020d09050c040911012706030b0117160c080d0f0209010809010b01091202180108030901020f0102040b07060b0a2d060f0e0108090a02032505 77
    0x1550044003003100c845050003a04c841f40c4241182100281c0045481580500800c040740e000b038010041395580c406e10182000380a110a0094550440d01800340e00c205840d40a500e85030010030506000713905070401032240300c2c0e1400c400c094242c80b086400141d55450054050840c50030060b00052001c0b250328008100d1000850094142a1445014010144007600c180c0451101a5160002444445031032119409040510600f2400140c1ca49a0031400940b1008028002c00c81503414100203000710303603100d8114000c4134902000348c4542c142d00e00100704c0d92501e004010006036103030000442d0281c0004018210104281d0031a03030818070b904200b50807800307640682780140404005005c08902c440c0c001d04602c10004040e40c000698a511160085084400c649009881c0076000c02c40c040c99203203100014005800c2603c041c40803128014440c1c0680c1c00302c64140952400440c2500c030041008003c4181e0242c12690100d22400615084603030210130308250b1082d8240c00300d1681080e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 304716258 1250 304715008 304715011
    0x30c19021023070f08160c06050a2a0c11010e0301050f01030b06012a0203030c0d09051009061205040c0503030c0f0f0c010c0f0303021201140a060201150902070809030f031b06 77
    0x140d03680745e41c680300d01300092044480d42280104108403036000d4008281d140c840d803405074642c11000194200f01c024030000035021420b044410700d50420b2558502600300d60501c100b66406802884803000000051b52000c18001c2480d03003640c03030041000f000382c280341c840301d05032409440f120102e43d407980c00441d100c10491000c0b40740000d009680e40d804500c00310501c201c0500c003d041d20700304080810200d1411210b43c42d0180042d5981d2402c1001d81448401002181c2e19844c103802a00d0604401400c0700030206039204009649000060074860303000d0b40c10001d031100074141c9666500a940203580d070340c48540e1030ba450b4000e05079456056040080d00000c100010f8590940b0001035032200094103107601019028180c08004001422076501c000134081c0411280e019080c103410790074000c1d80f42c800d4004906680c900032100008070118680c400841e0300140002daa50020752501c401c890040485041c1c1520130408800800c00d00403028164110f07600f001101c001c8031441c40195034010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 304717508 1250 304716258 304716287
    0x31201170a032003130e0606070b06011b02040606091e0302010f0f1e0f0f18050f010e09070809160302010e010f0e0d050609010b06030c1902102307 65
    0x30765800c80000740240044144098001c640000e80d18601c10380c2c6045510211001c0703c1002400010310041034810f81c10341d0000c0c400c1c1c0c1c9081c1041f0282d03841980c2048044c0805061111590110040d0400601c1060f6170765030260050140c1540c804001e800b02196009030102c00200351802c0c0c0d104c4a0200609044940594541104940b00070f019100200c2d00b0f580401084081c00380e1400b044283e40070921084045c3d65000001c04100900901142078099030f071040040d041c0d065017068410010070000d8400481c0c08640117411078006842710403041c0c7c080c5030404140c2040026064220400612130385014043d5003014140444514a00c1110b010083c0802c0710226900015403040389006010303c100e08046c03083c149444005401d54a0703485046a01d54002c604101101a0030301a142580d18265400d40c2141400c0307440034258000e210f89204400c0d102c9000c68100c030301c2004035021800c45030381c08021440d2002d00f000c501d9050080c04044268200021802c0d440c0304440c41d160020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 304718758 1250 304717508 304717513
    0xe0c100e0a0b13031b0f0e01300809010c050610080c030715030f0e0f0a020102010b0411040b03152d090727170c0307060f0807030b010311070503120117 67
    0x181556034101c407072041600c089038104641700010034858034024114001e00150305e510f685030740c50700c03082d801c12040501c1e1503c220050f00c69480c00c000c10242d00010307881c1e070003100725885000060049900b841d4103540580b051080506014030120f0303456035072040d28800b6040d1896189074070145540c0b00303c4cd00c12b41c20321909103164401c050b48aa4000a4829a000300c0410141c80e6000058039050b100c0c031851100d5004481d40c41c045603024442c0d49009841600d0034130044080e058076410a00442c49040c207818070002c00910590391000034403c0b0072500412400119480b15a4551842c803841d01c5920039030b0750102020820b2410640c814403488950b917030340304883da120503140588483e100d5080c950705107001c80450f02d00c0900740c8031461a208100108038030003058040500c0c02007075034081020712008034241841e00d0740c0422120b82c8010035040200c0d01141038001240203250640f4030b03609294000c00ea00c410400d000c402001490400c1c541d482c5140d03210300040079030000030b050450f000da = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 304720008 1250 304718758 304718797
    0x608070503070806150711090f060303071104091703010305011a06090409030903061112010504090b0f090705060a0512072a020303090a08010501060221030403030e0c100e0a0b 77
    0x55100c1d843c16030344030002508412107414114000701c1180c000307890840702c1650000d11038000d0700f03140c800c0990001000c8815206810310710f020030345030310490102502c0c40340034080a9815031910340100503816808040c1032082c1d0b0601091803016042070000310784c01d50070000f0000d0484004642c610b100407009103100d00c1d1160140400009040442e81102400300b144000000b10720f140c41180c80c481c0604200c40ea0318206150380b0714200c2e4050301300030300c240e1629191101103501c80001c20b9000360607410b503804548460881030319190b015806a0750103034000030f01c1380203030354044042d0521f01c1c0444040c48042d120305405844a6810034404400b034006148899445401d0548012080e8005010390b4906107020b0041184641c4d076030800c400f0b903911440100702d242da0421040840c650300302001000c0402c08003000483c0d01c80070300007404164460080300d1240c030b401e210290441800600c00c42c21407001840c058113140100050601c100807190000880101c010112240c090711054005080c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 304721258 1250 304720008 304720021
    0x10060e0f06010c05060c09011b080d0905100203040303020d0b040c02060708070302040e0405010e0d050a0512060a2106110a05030c13080a080423060901120f0c0c0203070608070503 79
    0x444006060700d0400c6030704050721002c52405e1103014000c107130340315506a0b0350440c84001742140d240100e1469480c3c45070050680444d0814003501c07902c804988001c6050704090901a1515110050340c0c0412440001800701f0180c0683c0180043c4848120500540ca900c5082208841445d101071025030004000150486d1040c0c1441d64002001c1c100141002e807500c03181c0c3c030001d0301110100c940380e41d10a00c6010003401000050851201031400c6458201d04c2000184207001300c200502d007400241c4003240d9203554208022021384901c0318902040c1c408051403001081c4500c106417042c51901103900714540f49207003140c0d0308107074644525103941c55042000516030b1120403240110725040c80d02007030076201405120707103090144655503211420003503091340041403420070b4203085524041000c519183d40058071182c0109003050714020202500305000b503c150a55607940914105c0740b144940c1d0812180c144050080e400c83d4041e68581d141610909003d942d200080b031000d2001404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 304722508 1250 304721258 304721281
    0x304020603130312060e01051e010504091e11070c080d1715030601080706090806041709040f1d0606090f180c03010501060e0108100302060f0d0605091810060e 70
    0x2c240c1c0300b464501c80302c0f1010038280b07040b03410982000000304003a100421252420105a07800d0b080f0704048003e05141c40310000c0c0c410f1107540f00c0e000885407185001c150440c9404030302214180c1c10300d818481c81d40a11200c0c502e07503101c0d03a0100c4690100e00004039031584002100c031740c030700100d032150f550485401204026004000b8002c07011551459221043e41c0c4051040720300a150348402130a200d810140080c14501d0b40e0341122103180d000b0400c000114000d0304440c18014401c0d0340f00380d620700141e0041005054158681041d86003405280c00d041000e12451070000b0a403e03042e141541c691004001c844142545d003156080301020104903426042c40303140030031090f03000894480f00f40000c04203007513035000d034400740106120017501c041c07030358118142c16400101c1c10131400c200ca066030700248a90203010340342c5000c0d040c041000c0341e80e881c070356110b81d02428005101c0001881c2c10102600c0c3c01003104030810050040c05407960510040b40101026601b08070b0850155955150b590107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 304723758 1250 304722508 304722541
    0x601090905010603080f0c0609061b18151801170a0e0703060c0c0c05010509031c050d0f020409060b04080a06022107030c09052403060d02030d090303140304020603 72
    0x1e4095580d41400000103040c100200341c3c41700142134241d1650006152a4142007000300307042115000481000306150851260300c2d4840c54400c440c0b130300c41c0014058200c92002c10201c0a411807054091440300c0c4030040d002e0302408500c500c40d41011080d090044411009800004044074071001c08100040d0342500640700030201d030011102210b40d2a141c18003601e14140226021455117031304001440050444040a80028208030f07203483c1410010940d1461101000010070074030200520030144260201e6444028404040c40342c3c6581145200c000d50192150140c180d1600c0710001c0e084001d807054804503805100130745425009515030a0180d03102c00a200c8010740720521504214107004079040c01031403650340c0029200090310010307044e10a00c0d00b10600c070340140e15903281c40c60120401010b02000000c1c105850f526060003140036880300030300007541405042d50400105034041c01c1c2178102da009540341c0f90740ca488604420728610041e18042d4004104100084000c5141d00409 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 304725008 1250 304723758 304723763
    0x327020312070b01050a050103020c03071518030305011706060109090f0b21060c03091e0307050f0d0810120305130512010b010314090601030b13120f020d0306050306010909 76
    0x3112164494000304107241c0c04010202d80607280c2c1001846103082c205000ca01508080c03d04525141051440313541d01c0c000c040c4014032000200c84203d0468405401c510b50340160318104131a083c40c41d260141c00f8040900034507003d844070003988503444d41c001492600408042c2c480301142420094040f014103004495082099122880404907880720804003915818910b00d04151501c2465031505000c005815203240c0c00050007400b085a40102d6001075003000782600405200c40c69105608600aa11300500075001e200c048214404020543e14025030040c0d81d6106c03035607619510303041100340f0350095064601c1d460101d000064010401414200c180d903418850a5a85200007140c081c02002c030005543d444d013140c0090765130140640340c02114950820304803413800b283c140e43e231000140300c041c140b10700400102d900c4a05c85284500b083c0d07004079410715400a000c0010342414800148000103104041c0c1185103d0320900c41c600a5410080c040e181a03440e012007a0060900d4200a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 304726258 1250 304725008 304725013
    0x1140c2107030e010c03090209010b1b030a0f1404270b1f090b0301151b080304050c010806100906050d1508010c03061a030c07030c1a0a0c03270203 65
    0xda098036940104120320400c01c65601003050380a40e000f460035a28011566014142003040302401aa10b1810840c156100554155190400c1c0e07400c9a1001850b1701006441d8003001a445191950040e274006030408140c880366001000c1d1003010318544038030700c1800c00340d00c1000103680c80c4110722510450068090040459015210b100041c0d03084081d000c217421131034808482e0340c45240c12076919402005c100009505540c5000170340020011021421020000c100742500c0810565411100016030825075160f10b80c41c051402c03c1e1f544c9020303000540803d000000040040c17070088921019003900395a000c0000703180c0807084e603d58000b1412121825110700301003a10051080100c001041000000301c0c0121303461002800300c400c01d4120400f5480768a07907011490300d8040440703400c60603e0860b26564042400c084038100d40003107000b4208034101603040143c500c54808039000300780d5514100039200000314141c0460b403074000049204142c101210504110152914035206e0000d000e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 304727508 1250 304726258 304726297
    0xa03060e01140a0f18022b0e0f030705100507090b030c0c0105011203050d0908090d050c0a0f030201082409010603020705010b060a020c01140d1508190b010b0702031501090209010e0301140c 83
    0x1f148000300322010b026001c20340c1d507101400040d03000c00c1860001001d081c055480e08210341c50340381d20340000c40d24000d05aa01ca8011518152140c0034040060101071141622810400c01d922030a5205a0f000d500340c1d07080800100e84848032203686400c039035040d02e0b9180790603034800e00c210117401400070955504409004140540d21581e9204417180c4c401c2014040014840d4200170011440f0780080ca8a501660428801030f40c0195659400c8440c1c15007400e02802003c1e03410541c200c070b40a040d0b820080d1040001a0950160060482c840c8030301c0c02031107900625030a02c84c540c0910a00100141e100c80c150042650288619034881c6d01036249007440e01241c4401c0e481690418825808400340c0d00707008001c0504180a96103000ea28115841c40c01e540d60b4603041180c00e018052103e10000004e0706070210f64007003003055080c440c6001b0382c0400d503a40317100101c02900300700b030134a002c0b802c06c0c1504400d42c0b03011311895054502c01c2c1104c03460398881341041583d90304500351840080e2100720 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 304728758 1250 304727508 304727557
    0xa0e09060a08060a061d0402210102070606030c14040b0609060a030f0513050717100209060d050a05010f05060910030c0c1a10090509060105060a03060e01140a0f1802 73
    0x86564800c032422138011079914903107807104131102d5041700e60f010100581c20900c001a0b503034802c0c078007102d601c078a040c1114103070f4044004c1c0240701d0010001c0005162200c000200242181400c00301d07808250000300c43c1a0710700034402942c1d52106010b9200b07504002090452600300702408981505c0e250014101401d02008011078000303649410083c884000240e0030401d0800184006d01a1242d0881d02400e220390403d40e21030501001caa8107640126402c11103850b0b00301070307a81c1d00d00303a064240010709200714118014602030003082c4c00c0505100012a1a0601c0d200700d0b08801c42c00780507405404421442100201200f048090420406101080c08203040b00c4074101c900d016094098124100381c0c090f8004950b0a60040c04042d00348000c01c04030346808540395046031400c0d1401c580e503080022040340209541e80183d007081e5074280010404448007411403c030802c09450541c201626402e140084c2a5607115264401c00c0c0c804d14032030000c0c00341d00507050542690421402454210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 304730008 1250 304728758 304728763
    0x51005011101090b0901021e0c0d080c1216030612050a060903210b2b030807050c0f0606040b0901180902060904060e070801090507050a03020f09061b0105060103020a0e09060a08 78
    0x9456401c2d243c0e40218424002641c2e5507405009031280070005171030149912227141d19400c51400403401d1003a40720000c2c1100d28254219202495074040c109140d00d0a0340264400e008200d000c64000717480c10b54081003d00d052149444010b4000000341084465603441002424101c8011410048510f001c007070041c10585a25004c00500903001c5806035201c01442860400b50b44001c1c014800200021100e4600c0d990740461150980740841c1c1030758503800152181d12400d00720309100c2c1310b4440641000c40010810501a60303045400348200d42600c8200255203d00380200c4445500611700321102c001158031022429101800560030554500300290840c0d81e9944002d01c06c1c283d1408022140f640704013014054444020100000d0070081e000403c00c0c003c60124505060b800600c3e20b0880b80c110042e20603002008105694800343c0030140d0310031440c4142442001d42c06c2201003400c175800380c003d8803c811090b6407100c0d09180300b90100484001d001e09102d80019500d5800b0880d001e09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 304731258 1250 304730008 304730011
    0x92d120a0c030e01050405060304060513150b0312040b16030207080a08030f240103020a090302030703050706121803120902090c0c0705040e031b190b0703050105010201051005011101090b 82
    0x2140c444403001c0981e0704025003d000e80c490000d0420408100612240d911141038030740003600725a00140d59507030881100ca40480740140580140c1d00b81c0b01a55103040c0c19007101422450076026036042401c01d13419050355004502566454040500451918581c1c021041000328040d2045032010b560b9440b1003810a840a141035900b00d00010410244200d1101c146810a1158034200f0721a0401c4241030600c0c180c080e0396904240d00005c2d20015035100c0d03a0030a000d1500101551031042d628036280fa903034011446a1404181000d140b10025002d910072202c4c960b084120b2036455070301d2035804a0f4204d440071070703400b04150344071031a001680352184814825200c030507589540e102d101c80c00c50715009565000d41e01c07442c103144444445c8807021003642c40c0b80380c6990035500304150404007581000d4038204805030303076582d0b01c0c490b1092040d640d01c00781c0102e0307658408110076625603004900360307807003118003140d803900140080100e940b20700c40054916004200014100d450303540c401070380c03c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 304732508 1250 304731258 304731277
    0x30f03020d1b05100b010c0b090a051504030906050702150d091b060e0906041803020303061912020d06150f0302090105060301050d060903050f0a02060708092d12 71
    0x260500392003507801c00c40c1d6010b9a458580c1410101034640d54590b640c0781c00e81c049111458840355252100e0340641a414038481e03000114142c1032a01050080e5141d21155041e10540300c3c040c0d841418625092441c1e000725096920303800ba0500300001030301d2039440100100d80041812103684080340624018061400242d00046030380400e07402d180c50060007003120b0700d04104c1c10390003c0060795004141601d00f070b041501d904403d80d603080000340003040c10306601241c801c001244041015404070081d0300c07900f01242c003054403c200300c0023109404058081c140c521810b4514103009440d04030030985403a40300d0030003c01e166400c41010660000b4550011a16804034102403045140c28101c0501500c402e0710007900719031504000804030f07040003002409059035a0482010f1512440c11546038000e0403080b0b84c1e8400040c4002980c440c012604034000418010100b003c2c038101017101041e0952540900c080c1c0c1d030407039007918040d6103003810801c018032481019045412221010340840c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 304733758 1250 304732508 304732513
    0x8060f06130207050f120f0901031109030f07030c0902040e0c072a0f080303060d02010c050a020a0f05100f0f050d1d0303010e010e0403090308070f060e060117010216110604030f0302 80
    0x80d20842542c0380803140052070380344c51001e00047c01c5e0b0204081c20342e902c5a80900c1d02044511100c11440304074401d214100d50140640715101404c000d0002c7d8030070450340704818001d12256244504003c03809640210004400c6000c04200000b02c00300180c80503d003c1c0d142d21031400115141c2d4140c0342c8040306480d2004002c0c050030007000604608810003000c0b2400610701d94a0800c0000f00c0c0000c0e0450001e040c00400744400b414020100400442c42d94060414005552200010220042c4074440c01e41324884e5018070244081c0715507120803c80d07602c1c2c0c480314088015490240c549400414007070090300e42d40c80e507000c0c640001405015035031200354065036403941050303281c00c1c0900058000d011000359010034800000e074458a04811242c22051050b2101040c2c9041e408078a0704d12006002242807801c2000b0b000000300c0c1140c12925600c5040c00e551604420081c281d000700452405030b400701d200c1c5280400c811620f08201450700a0605203040c1e202d82d900d44280c9600c280031390059 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 304735008 1250 304733758 304733773
    0x10303050a1b05010b12011b27090203270703021c0501090803100f06050d050c09190e1006050306040e1504120912080714030c12030411010908060f0613020705 70
    0xc0c01d0203403042c0c5c040d2481c0c2000340001010950f5408d40c48046051358010061880500c01780c1e010900b0110381040030010001c5000c0740d88200040c0690400d980318910036040c41c04200402c08034205100c10a40090043c003240d40c03550302000040d40c09030400307a143c1038211019100189084c4248500f680c401e10030720792030382401420004d21800786d410a00c40941c803202e00b404016004826103150170803080340800d2640d20340300b2156031400f03080c80882c1c220400c0b00156810b801e03d487e845040d1811400c80350542d6861071307484810700c5060f2085034007040b800c0001ca0082c3c2041e030084a10492a03c045039034004c9407031640e40341da000c100c03802d5442e4003000d85070900c01544071110000a0281003802051007009440392125031107a10030082421070201c80c01074524000344242c2c1c00b072000090030303104440c0030301c500c480c0c04ea842103604451342d035406400326105600a640080548011000a0130169a400151a00f040c2c0c0034203103580c810083c5042c00d4100406000408a80307101d40084c1200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 304736258 1250 304735008 304735031
    0x21215010e1b1608070614061201020a120e0a021c060524040e0a0b131106130b0c011107080a0210090b06040b0a050a030602030f0717010303050a1b0501 67
    0x1401005001c0c06800c8000c01402c1440d80071038801d8a980122050407200160003e14103070515104039240181010305150300d0070140c001c500811481604259280c003181d03800320110900701d1040c1480d4038013041a1400001c01001e25901100702c80e0b40c048100c80005049400041540d85a020a060702901d0b801c040d00802c289401b03a0f9810901442c0802660030070810f84108080590005130b010301c3d0744540000251408207c001c2d0840d40012600840c3e080c20802c00c1e842101c0c80d1029544600c107c0a070000b5418000d08031050b070540440e514405608005101e0050340c40709841038550341d03c0d0350385030700003541e800c0051082d64400c0380c10540e02d6640c000b0107420030004c241c0b02480e441c5003007041c2012030740c4c0e1130240313a20404c110f078005115402200010320201440c0c2009420010040d000f00c00c0215603802103010300351210b142c00590f034842104484647c10408140c04d1311807140010000070b8010700c00381c42c290000d4240342c901c12101c01c0d24051000e40c4d40c1d205076042d0f03441c1c0c1c101021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 304737508 1250 304736258 304736279
    0x905030c031c0905070e0426090307050306010b070212070f06030204050103060504140406020a020321090705190b09011e0e0405060d020a150201020c030703081f0e060d02121501 78
    0x1046103202905020300300c103a071203550701c1d84003500c1b41480d850303038080029080004000c1c00e03102107003010140b42c4500c841d040104219420040c0407600a101d10702000c00da5250010f2007a0484030003055803840c2500b141e0900c14201074403136102103035104240c00071513045620f240c2c140240090307640045e1910b103054001800d13616140d1003640120b10740302c14481c00d83c01ca2000d45038032a400c1813002d81d0342c0081c244102d103188241001c5031004000b07400501000040f060106010302d0041080750b058a0b1600200a90710145551080011800047c100b003050400000342654400c1414a1542c1911000c0124655410301884c10000343c0e82c07000c1c00d21980380500c42c25030080b0054800c0c0960841903800324040540c0d03401407203018041409030105e580d00c00d404803420508880240da482c3c101510f0050f040c91819900300700c0c41d00c490350141381e0050781480a40c040b1024030031004800d84881040c00880001d104050340c00450344480340d9507400301004800e0200192290b40201580f40c04030010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 304738758 1250 304737508 304737547
    0x3020c060150010509030307080409050106030b01050a11070e0c070309140315100302040e16090c050307081905091f060522020903160e060409020a1401030905030c03 73
    0x410b2000303200b400c445880c0c10007072511440e40c1501d42019040b01e0030700042c0d81e64000c88424940c107100007e010820016000058003c44510a0041c13040f41d8a981058040e903036000f01c0d050000381c050101e03108840c0b00e006d50204900040040d60f00080c0c40d00300c00c18095404544400050000003420350070168858140e070020000000100c0000b804040080d0312035585043c0c0740d2490031500c0224003070041ca90400350003550700810410007618072039070700c0380c40b41181c600c2000405500100081c1c00c01d91030194449014807980c8503482d40d40c03140819a0302982c00780040c1031482001100c0162400d05200745070142001d440145415900e466100020280f4100541000c81c00c00c2c40c02c11003070b2142d684620780103030082101e00c3c00e890010740c050002d000b6a101c5585c10b101f040c01c008421b8140721020800d40d60340200049090b51100c1c1804161364031510001d4105881803000c0014040800b8400306407d014034000c5903400190716118a103810801d055000f64100140c0c481503441080c0340d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 304740008 1250 304738758 304738829
    0x412080a0f090609121e03090806010f14090a020c0f070503010b3016060305150103020c06010302090c071b05030c03070b040b0f0d09200307080c0409020103020c0601 73
    0x40216040ca0f90042c00001540f2070015000d40700040f003410004041842510891491140e04841002c1d080042413070460303108040040c010270001244066080e45d61805413003a00b240c50161116201c28130804001c020241135019500b480903038066081401483c446014840051035114109002c1508441c60302d0281480b500400d04280c030400c2504a0086111a810218101c1c41840c0030006007400d08245240020611040004ca001034055001601410b15070302c0ca00e81e02d441c8080190200c1c0300d91485244564840001040180383c080783e02c581c80380d460f038107590620030b00c1d81c9d0b41c0009911400f075131000007a01040600a83c00d00704107142c0903000817030003003190034941460a85c5520640c0a8060380074000101c03003001303920705001c407100486000e00802581c109402c0c0f00c1201d0700c800c0c03c80d0b15001180300901d5030510f0300241003811f487c084000341214440140030000140f0702400101c0c103041e001c0c4130785c614444051040c00d00a01894510344001004030140c04080981d14040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 304741258 1250 304740008 304740017
    0x50f0106051c0c0c0803090607020601090e031804020912010b03102a090302060304060e0d02070b0406120b030303101d0f010501181503090c080f120f0412080a0f 71
    0x80c0a110202e07501e280c1c1c429005030000145035100c99204554060500c2009444007000100b0722089240000d01c4900c181c2c5035900b541c07903507600d8902c0340c1c0544120380c500c002075910034017003c0c0720600c860040340c40c03185005000619103003002012030400f903c000c5481540d0303551b8a0255406040c103101080d81d003030908008004000c01308100c24241c10011021001907031031004500da80f2070181c4a2800911740040806460349405d18011b8090401e800d070010885c000c0c000d06400c2140002400d205840803c0c0c682e074103040c01e0601c1200e0148090081000f140d4448a440702c0d2a103050005500480005018100260030305240201c2c081003002c0404600c1402030421007450700d07904910341594001d00e0f0080060306488905274401c1c826030045200c0010182c11010595010f51111503036034800c020f03a14066640d0007006846640c4c01d00b6080c62608030fa40cbc88140f14020710014840e00006044903814640c903204c1d0385d506082e001204a54609000070392003000c581200c25005010751a00d030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 304742508 1250 304741258 304741267
    0x2d050402010c0807050a0506040b160c050d0e03030d0606050c06070e2d040c11070902070c14120102040906050a1403150a0b1c0303060e0f1f05090a050f010605 70
    0xc010b840100d001404400c3d0104a510801ca41071000d0140b15811600302c07082404d1074240344082180950b08011000c4960268100301400340c40300c000c0f982c1c1c03c40080c5c4402d03009441c099504044500c14990f043c0003c11000c205229540703e1b20b0050001c1d681c4841c0c0354030f0f0440480c0d10f0316030040c089400f80300d00b90880100c503548404404240058070040300056402c0c0491340c8071080c0003c0b2841d5401803c007403040e144154419441421001700008a4502d00c0c2e44044500807031180031400340580c00111010301800e1a12014259503280c081c20380b0b0307103882c0d400821070301f2600036401c00403000b0b03102d8104021529050242c500907001c814405001e40141400090f074940310800c80703030079138041c0d50001051030080e68084820124043c0c05581003a030800216009804100800c4000c030f4075000c400300d00b00003401e04c1d80340b1481821400400603154100c429480a81c0203061005030800500c000c5542c0c0c407800e001c5401822041c03804034050602d1a00e03404007400580294040000500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 304743758 1250 304742508 304742513
    0x1204030507060f0302041706100b0a020601030b04030507080403080301050109050f09070807050f0403150f090b0f190c0309110f03030703030f020904020301170609160e10092d0504 79
    0x2640d80c00b12092410260502001c450059000e4001c030360040898080111658a0000b808a0010301c00c03400c0f4983c0011030b41c0c45a401c1a034a014281d11500103a10010050000074480d62141703400c40e0007403d02e617081c09a00d40d0340603170940c80b5800c01c559000c0048010042035800c00c00e401c000d040126480f00450720100c000c03528925000b0140410000c9441c0800c0515000f0350403200010001c1082999554403401c1400f520100100100740046c40c004086282aa642c0f00781c081d0a60701c0207590046032600c40318241c00800c060b20a6150000c0325103c10301001040c450045004000e440c003044510701420b015246104900c5064012110802802590b42d0301108644c880d9a0504001425500c480c00711402405500189600244000004078008600643d4501c1214040084039402c0d9651a2202d88811004103a070b424550100b40506c0b04021a03c3d035294040404c0d0000710307500d0303910308242040e1035000444007000c0c096011807007412034503282e00521202150780144803504299 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 304745008 1250 304743758 304743763
    0x70207080c0d2d06020c010204051c0c03080706020903030307090e0f040302070504150302130b1903020315040206070203011d010c020601050303160c0e0109050a0b030f0604030f0c0f060204060212040305 89
    0x450140480d40c2800500071400d40046402281150090004c46d01da20410351014001d6200d4064940300b0001122060319501c5a1182c50602d80e60100700c0041507881c6036a501b01a07000b2290031079003540c017407010b054991800c2000c0c5200300d1140e90390510075844c200e4040c110010240210854285c0d440030000802d13000a540c01c00c4032801d84000903449070fa440007240c2500e0940009601c488075000511071071701540c01940183e1400c9400080c44482401c00c0c504080e6140710080d055049004c880c498007110a020a50107030001c2d0146242c102d0a600190865469500e0340c55402c003400883c855a007024441c03c0d1054181380020203803075041400003a901c0c0603905841d41e5070255900c50790100f0000041000050604041c1c0e03080f90350f12211100003500b411a150580d540c5080d0403055030745000603ca001c0313058090f01030403140d00c0d651021a80c0c42c401668000a002c41d03002008005441280d52035002d0b80910001601c03107040500003410190641880384903840140030500115001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 304746258 1250 304745008 304745033
    0xc03061107030f0e12010e0f060702150601230a020f12090306040b1003080301090b032407081f0e1602010b1f140a0c02040b45070207080c0d 62
    0x207424041d540700c61300d50001e0203110603481464040d50a180c1450004000011204100900e0307200742c60403550707103c000305d07074423081820f0740d03040800494081072895014914441d42c00c046601c000703956106c2ca01d881d84103a44102e444100681c806a00058000d905000d40c8054001170b809540c030380810080021f54600f0060809007101c003016001c038000050701111034009640c011401c684960b50b800a05004000524103a406405803002e8030091211062504070004401c20031240b86881c0d0180480704054014005050140c0c2c10030040c6c00c100c0400301a02c006c100c01100b00310309281180294406201014900041d6030500c1c5070900c865542c084421030f02403010005601070000f0350310490704210004039000c05c00100040c280d0324642d00200e450022402501c0511584804e03809008901c024078005150006408203480d00b10818045c24220302511a04507051180d544440c0c04400c44040d105040964004c000401c8402c4041c0409500c203501200d000800710901c2c2c43d01d0444111 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 304747508 1250 304746258 304746287
    0x3071a042a0311130c17090102030115080612010204090f0b030304151b02040c090914010b04050d080c1005160206040308062106090d02010f050112020f03030d090c0306110703 77
    0x243c6640d100b405840e6402c01c20340d40300380726405014001090740050000345800712100a440c00c43c00000710034100500859049410150501510556507402201c202901a01e100d900400c03407220241ca01d01c007400508040d1805210004484a5000759001112009440795009070000c0c4020010f0b1000328405124018082c01e00103070b841c4d810000b6411b14000d02d640203612a16108120b0400b40d03104102c4419600010002c001c181e0f180b50180544a03000d04ca00c1c4a402d90800c000e0101d8140030400c030101c280314421290604581d4014103040c100700c1404110501c5c2c2d075070100602c000701c0401c09200c4903001e0001d0907090620351002080800d00501460060350812204003032403aa04252203a50380910098600c6401c044042a450345420400341b0019800c10030752112100345441400d0488240e041c0882c07003901c0d16424005c01455101540e80c0c940410711641c202c030099401091649445444490007160441c60542d04640d00110a443e0000c010700000e00020b03088000c4003030400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 304748758 1250 304747508 304747523
    0x220f0b0d05030f130e01180507020a120f11060a0f11040b0f070c090f0c02071403060105130204170a030f030203220507090f06030b162003071a042a03 66
    0x244100045075204d0294003c4418680400000a070402c0c01a56503031140c1e08900c0901540d25200c2049a03509132103140a0301610403800d0026801340201c601542921503401d01c20440040954400d040060480d440120f01ea21120300c0c0b00110f51600c2014021486665104e051500b0003040845500844501440070310300000e492040c007030041151001044890004d2144540808490010f030040c00c0e1340c2400351060642c00320305c0714010490100b01c44000703001450145c0c6000200040c0d600c114900300c194035400c02c00401c1140d043e00e054910098210010018080c1c5854001e005c14000003507141011b205000b8000c94040d21040480882c0d1030310100c00d05010182003807800d164807907000c01219031501621484940b1260091400c0724003803203000050b40da808550ba9000c8103100303400c0c00000c010311a080b410728180c0c13460951302141c0400b16414a0565610070340c00c0444201c5e10702c82d40680204000402a8410460201180c600c403506000c0b40f103250300040c04021800b0080010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 304750008 1250 304748758 304748767
    0x3010f06110a020607050d112103060d12020319142a0303011d0112120513050901031425140d170307081503061302220f0b0d05030f 58
    0x4001041a41800c2d90001c00340d0f640e070090741c603119980b001c155103c6030101c1d0702a91000d00390b01c00454045031a280e00e404114101c00240038165140d072005140d5a8041a080d044102082074100103401d40c42c0181c00450361410b0751022403100110f4003a03142c0400c00e1800304800c011546c481610303000c22858214220b5040d07404000101c600016521602c00e1101100014a96081d5180d16043c40c0e0756400ea000145d88071407540212091007503000d003803010704001081166109100604584000c848008040b58444001580c0b400003a0b0050795440c03444018000143c5013401000d1280c000380003640740c52407161031020703c15071951060b07640c69164006410030b15103590508006441d44469103161224424145120503013094850300c000071507840001c4ca100a007803c0e0500e83c0c0000030002c00e01a5240380410200411000d0f0898000d10301c02e0707040f900f007207032190a628011420000481d18031085443c4004480b81c0304242d61140d83c100c558040031034004401c80c0d190750741c0e4035030310b43d41d9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 304751258 1250 304750008 304750037
    0x21070219081210090f022d07050106060e0901050d0507061d03031c0506030d0e04050a020705011505040e2b02120403050705010207050a030503030610020c121c0503010f06 75
    0x2406282c0c000d045110040d000c106000c102c41c0400c100f075610240e130402580c82c80901c8017080340202d040d29500e03420021030215021402e104040c050345206800d89260000b95511030b400d4a10036031069011512150505005183c2040c02c1409407000b542c410a2184068540580d80c10144c4280802d03c040d03c1085103002ca520701c10402da4440240840759602c0040d02c50000741c00c0d083c1da0341c005003490800894420b1038080303000c03800d03014640e80704480004080e007040b0050102911102d0113540c05c02c04403002074420b0203011100042456810b6040389000180300558030450390020154005c512100104901c0703421010304110541120011510840300681c80d0013000755205101003c00714000081010010303d540c01d07900c2c2039081c1c524680e6140107100010061340002081034000b4000900c580c1040c8804010260b05441103c07900070305800414800ea0301004048480c1e00a15002140680e401c009840d5800891903c0d80c07540d85001003400008919001c0c071720403c50b440001091 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 304752508 1250 304751258 304751273
    0x20304081e0c07030c09110301050303030a0c0302070c0303180e19020d140c0d0605010504050109060e01031d010608070b0a0f08070512070801050906041406042403050321070219 78
    0xa4602c1d101210b0b030680d2241003440c50a007586c403c04881034100414101301c45101010380b812100081c000758150384821300e101020b4800b84102a04140e0700b03100480100348807904a000840c0642c0300d00200b0030180d403540409034001e030400e4282c048800300380038005541d080f41d098010880c205c01078648003100c0001d030140451180e060703054990381003400b0707800806600074510b042181c0000c118030b60380e807070042d41d243c0201e22079940443c08000342085068050b6440a060743c4e0140f40c0080c400c402c090040c480741c00b6072001891903a40da04018000340400308400809007514100c8a810642080c4005040b8446200840d0402c001e01011442a9005000b0349450420004040c4068a044000204601c000f44549803007205010086030b05410b140c440c0145078901c850300884c160741c62405000141401c10000c03d0346440d1900c00000042030000400d0295124001030356480103e40070390350044d12611301c0c00c9075100c0e2510510107807a40006100000743d0301d5143c0c48400c00e400d0b0270f1851 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 304753758 1250 304752508 304752517
    0xf122a020d081f08011109030d0804030c02010309080d0504030f14120103080a02030f0703020a021011100b060d020c0703020f1215060409020907090f08031819050a08011e020304081e 80
    0xb06135030070709031258102d09106d03025102c4064141e04a412141b0488000c41d80c1c0314040c0c801801059081c20351101651094116100f03003070262040700e16013444144640100c0301d04031400e4000580c43d00d00075215503030007000d00d441e001801e1a22807c2030180303828101030a10607c4005c00b100800280f14044074000d2042d26040c110340c0c243c0917158005400c010f0749920380594201c0c0b0823a48240c096102a020300d01400e82c680d4448020500841030384110001040500c0026510a506000c44060700320f55000801201c1038440c00303440c0042ca1343c41842081010001002d100e142c1c80700c08006910400101e0706a40c019042180d11280c46500108000300403d140107500226440b04100c211500052034a0460740000351003141c184d51080c1003500c83c090140c91a00810301030751401100d1502c0c00c400750301e043d50754540300341855948001802020a940c4400c1d2580d443d1801e40d1407018441004c3c0000c01052802075145260a6a0300d0b9003e1040e00c1e403210301031900342e1042c20b00d080003000382d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 304755008 1250 304753758 304753769
    0xa0b0a0903020604060e090a020f071407120303090b1501020a03030b0a1802070c09050c07020f03120403141c1e0c02030706050d05150a03030f122a020d081f 69
    0xd6440b41c071a1002440b080d1546c001d5030041c4411000714507220320b40e200b2119115192466070f8100003081d03481000c10980446c203400b162284100119000341000c0000c8510380c03294800090720b04040c42d19009600005181020302c1900135102c02c01a44c0120b42d42d9011980751030001241c80040c40055072010803a00a074950301204215405031160340d5005040e000d00031282d00c81d24990b245011f8041d01d80864803501701c800140f1000e401800c0c00d12103a0b5800c10001c041d9141801e207080ba410964200390300580d29a030180c509600040405d004030040324001003000d001c0d2840c0001e000e0600c41d40c004803040c8480381403c424034182d202d002a080b115074010140e5034100d0792004c0c001d0250304651001e0f00080c0c6040042034000702c54450402024402a001805051840d10305646100c00c1c82a000305214050708011144495032150814605495029082d840720141a4114826800f082c400540d40b001404011490f040030380c40303500040d088081841d00254242011702e9441c160b111 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 304756258 1250 304755008 304755019
    0x305220306020a1d0a09020a090b13150206010506040b0a030e1507020c060702030a030819050405060403080601020109031e050702180a0b030a0b0a050604060815090609010b0a0b0a090302 82
    0x2004204080d00103002c03000142c4d40e0b0f905040c00034543e4400c480c0609400f5603006003c880d0801602c05590040c001d10f203540d003402c000d05646c4051103112688041c041e964040c104100174800750721009004034284800c0d00c01000b856042c20f0210314184a1401030140041003c504400074511903007144038405444000c0d0b07035008000100c6622201422f580c030002500071005018502d042036001c0c1e41c070050b0000e005001e01c03000e03900c056807440c001803d94080c820000c0d006004401c2c460045078090b51285004080a1505003001000c121003e171600c1e0459040070204004a580f040000074040b5050720b0850401d00b419005440383d01c160b040081d00709040c006100c60422840241c6441380039280400c0c0004100c02c010507460b2499040024107070190040030a485071340982c000d5a01000c06800020319588a0140e40e103040d83e404c11b14a81a030301a410031003880340600003035412020b031000074070030020318400160809040b405082070310880401c4044086104440000046070051300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 304757508 1250 304756258 304756327
    0xd1707050d0809010c09050402180a0b0406020606010c020d02010305060a0f060302040e06030a02130f02040b0d050610030509120705120f0705010c0503010620070506030108010b040e0c0604030305 86
    0x8146480c1e640e00c01440d400301c0e1840c2d000840500040c000e060240c14a41d59040c0024240b0003000002d410580a00f45101000740840740c041d1203c1d101880030780f00321a51035484074074040c0020b1070541e00424403070400c655511601d00503100c1800311b20900d507090901207000d64681000c120f90f2b4105510013150303007040c07141c002000c42c0c00d03500600984507214030b40387c1c950342c2c0d91702410340c0d46907080802908000790f90030403042c0b20b196620184810320411401341ca803940c0d840050761141c00c82e50545004035529820700c240e62410055130901e81c91581028800346c40c2114500c0d450b03401a14141000c200c0009044081080910030340403d40c0003d6042512080b640048016503042000b0444056281c1303500151090702440541e412100345030b451015800e002510795590500303100b880c00842c400e8030004070300c070340d10708024601800180300002014034040081109079111001c2c0e15410390005200d1980707079260081202e00f507a0301802d1144d0b488241e003001035080d0308140400301e0b20030305116 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 304758758 1250 304757508 304757513
    0x170a02010e240f0c12030f070810090c050a02010c090806070f14071110110304060c03031e150f050f010f051204051c050a091a07021c0c1a0304020d1707 67
    0x3e01420400c2c03600f0048422464250180c5080c40c030040e078520064404550006501074410703069aa0300084444415400580e0b525540043e10030100c190b4012800114050304075aa09100c0c81000542a20f06807004600d040c0351152150009490a020840d140404c000c003a80038014242c0c20b44c8028000d595958181c4c1002d00c03542c603c20754001d1050641581d4140f81503c1003400b403007c0c40e4004040c515240c90301d941030300d040c40800801c805044d207407240d51070f15890700c10442111002024000c100040e001e180301d141c0b40701c80c3c4c00c1440c01c060795500134040360300c030009140c0e0151740a08203410055220700082d6514010f00564190b52120b2100b08410400042886440d408400d0010444c80024100543c0c10380202000072001444241042140358115030b154a806400301002503d800461f0b00031030025601c07900404480c0a0900000e030800001c030780c042c0020510742500e5240d588031414404054030000e40041d1251415003032030014400c03c0540c05100c200b810040c6903a8803a80d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 304760008 1250 304758758 304758787
    0x402090904060e150709050d020a050607110301060f061403040611030403090311060703020c213306090c0304080d1b1d010c03030e070503060c04170a02010e24 70
    0x15100010680144d00c007400c54440410b611601654070384e101c000711941400f05000700b840d0090002d980c0182c03c564000f66a440e008000c215040c068005100c16038400c40038942500d0700356024509107042c000003003080a90164070302d142c0e640703900002980c80c2c9850600201074002a00c101c0000c51000081c48101500718031030a044a110b101030014a203054030401815001d2002d02070f0141c2c0240102e13001510b40038104480c0c2001024480f640b24030341040d4285803105840e1460343c07043d820413086c610001c0e040c8240d0385004100b6000406881c1030390100c0e26041c8041e000582c0308001101250800c5650781c217841d240e010b884002c101c0042001c0088401002e1301551202041180035070751700c101d900d100d16110a86042c0c441c4041071a9580d4101c001b400c00c11060801f82c001c0310008109a039050120500820a400d102920380e401c00d01c0d001072404902e25686603aa0092191070010b03600040d0300000e4480031240f543c2c07110402140040121103e203280491150001294030044005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 304761258 1250 304760008 304760021
    0x91c050a030f0605150c120c0a030219051905030702040507090e10060537081b0c1b0415061d1219050a0f0302030711010509130b040209090406 63
    0x155600b485000d9510b2a00d504450440c05100d4009001009018040c140d107001020030180c80310441c1e00c4140f00910707810240c1c02000d101e07203544e0001c0901c00c080c5581000312030f040d894180540b40c64a1308954030345070780e85d915421014648a80000c6003050120600907a031080307030080c10500591070601d40013040700c20f943c01101504071002011a03c4550000050310070f81c0d503942c0f51140703042100e0480c01030f07a0040a2128080c0c8045010321040381100e170104180d846140d481d03103081030820348100c1050340e16903000075240040c240f00e82c00c020100004c070741d000f115441d1441800752000b580814007030300424110394070103401000001b91b01d95101c40c17882081682c0001492641400404204402e1020580302600368402c0b03840e00280110700141c418460310031411581d074150a582d81d040022030b05641500075810114184d014031540c80f4441e441081c09190107450540340d2000100c0000b0f18207149e100039962400b10380c04949507641248c10440b0004c140f4180d0749082d14110015021 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 304762508 1250 304761258 304761277
    0xd090212010c03050a0e0a0b0708100306110405090c070b0f0408190c020103150e0f0a02160b06100e030a03141318060f0f031103030910120e0309130203091c05 70
    0x1400c08400010703100480c4100d0900c3c8e00c500500243d45490b00e0446041e500502035903480ca402010000c00140307184110541b03500d480e040281c44610346000c1001c864401081000040e10400016001503c8100c0083d4011007106a81450f600d40d410002c1d44e074000d2403c04c0f0481d0703003012041c2000b1500007202012051003642c0c18000344074030207551a12034034541308005501c090f140100d004400c0e005903056000d15525001411310403070286108107004201c000360340c81401c0da014030010741804910000c1c4c4024a041c50140c0242207030110baa0b0350b428020103002c04c0701c0031142d0a030607205002142c0f18121a02d80100e8100d4031466a01d140488509454036810326090b0f0008040150709507040c100c6004001c240f00c40351450711850101c4004a102c10f51500041103410350340d81d46d0700a030090f40401a41c6003402c01c545002c8030000c44101d0540807419501c00c1c00064200d40d0740c01012005000e5106c070151312900c42ca01040d2805101c6072405840d0780c04050700f40318859100f009094140e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 304763758 1250 304762508 304762511
    0x9011e0b0f04060609091d0a0c1d01030b1f03060e030d050a06080703020d21030f0e01060513090515011502120703020318011209060501090c02120d090212010c03050a 73
    0x84210082100f1149144a9100070a90202e030400880a0641c0b04015140306510038082001c10b8111082c20b01c2402c03481184d13a503d988406114070f030444880404c9d521140242c030307009941107442e6920707885802050900c90703441400721801c80006d40c4032900c0096607c00f40034003a40c24407541d56a00c170740002210003801441c1c071000031481051405258200e8401d034019103003260854081c40000d40c2030b03030025124000745c40b00c3d030b0b4800102c107031112841c0b0189550020303804a4600c030341415120b070281800c01680c10071a0030300c0726a4441e00305811034014039030300054803002442c3c44c0d420020341c01101c01101c002d0500002d00c4c0300089020500b0040709074281c811105040c0c0c410f1410f40181c20005c0c00681c0107009070703540641480040c2c856510305041c1020000d807491001c605480000408071a40c54544004001e09001d50180803421a234500140184480c801d60301c2c4a28052004054021038503010800d06540320070140407103149902d0020300c401b018890000d0040c003803d440040d0401d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 304765008 1250 304763758 304763779
    0x1080c01020a12230409060303090e15010518120309032107020121090302010b040c02030a051606110f03011406040308191103070302010b030c0414040b09011e0b 71
    0x641c404240b00310300c9503211210710741c46554041d04603003296180700302c00a0030b01c1d044180c0c000c1e281d4030005070000742130701c4c50045005819407500600c03019503035204150f544514002d016800b541c08017000c8085d074007860603580b80e02e0080c2040b036190255240060300302000d41d0340c400c0c0f810004130051448060a404030313205600742c0c0c040e080c641000044a451125014001c14005601c2030303600035500201c60700c2a403d114541d882c5075080301c0d00300d074088001d80e542e981241c28500f0f107406040c3d1500158005142002a09213002c0d001c1d01c070314004010071800c0641c4510800542d0f40c00506144110440c0c40d0715003840b0b000c0c1d20026802805078807058800c0411200c05407800300100c8007940c1d0320a41c80c80c00c0022043d517a00da4400b0580b410800d04c8014480000612030030405820250b000b0b5001190320211801850305100c00c10006901450802c0040001c455814032400c0c0c0041d805403051b102c69840d8004140109010041410341d12445508181c00c8041078002d074800203001c5400f040c11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 304766258 1250 304765008 304765033
    0x305010911030d02070b130e07110d030204060e22140103150605060711180703020a03051501021c020a020604030b04030f031a360f010b07050a02040902040e010c0203030108 76
    0xf160110f401e000016400035005211001d0101e0241032504d50440032050700a840c1e01941100100c00c4480c0c80c000b400500c08050b00681c01c0240c1d4805000034101180b4007400c055000b040c1da0242988680138004400e000c5480e1001d03d0881c3c0168000400c0070010f000300000f5070344407070700280f00685140d48140815101410180725800840300010000c0385402080d582d51032001070307030304001d40d8407000c0c00104161448100301007500c160081d940c0103a076034031351351006802c0b00d00142900a50946070f122010003a40c000a0888804800d0380c403406a2207040d9000724a454100c090080d00444c010400000f000f00c6036410f580114800c1e1500c1d200c1ca054524100d085401169204154001d0131201c6901e60070240c0c550040445200d00d03102900d18201000071240103084500500801c6950800114058001085000d040c02c040d41d81e03c3d0200c1912047d035503000d0403001900c2145d40700c0034102195200d920083c40e01c1c180c0390007407200050403000652250001d118030b040c03a0196000e030315034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 304767508 1250 304766258 304766263
    0x130f090b0102031b100906020903010617070306020f1905041a070c031e0f0f031b05070902181801060f0302072d0b040c08120304050d030504031206030501091103 71
    0x658039041e0300a40c00d054100a44030400c4803034105280031030241704410518034201d8001c510426000325005039480c40d0b56000c2c10300b11003c2e41d021804a04400c00e22406407070340402d01804407030300244003603180c0c10900000c0013244143e0340c5004c020301001402505450b04580a8400c680356000c0d074800c0c075210003000540500c24a400200704c078515080034800200645005210106d0303841840403000c68a03238405031510300b002000e46801c030742c02d0440790815600c5000a140c0350a0480c0c0100522040e90300e86607145598040d40007981c0c4c0101d8056041c100f01065010300540081c02181d4011002c084650b100390203000d0400020302000201c10218003034000c0b60308003a402085580c09502c050062840c0108074030301545035011114003040814140c90310a8040c038062a408010303240f030300724071030302d0300d06a001014014030b01801040046980400c0e29060a00c1c0781c2804500e07681c451a08803030390180e44d51040380b5185001c0c3c3c04010b0060552200000a10480d009165012400308156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 304768758 1250 304767508 304767521
    0x3060b0406020a12032405090105030703030c030503060d0b040b070e0f220209060c0d0206011a0d05070903060e1e01141f0504020307120c030b01080117070803130f09 73
    0x100907a00c024041c0d0700054800c0c0134960801100c2ca000605145881d009004409100f0301462580e020700c039040c4030313a242100ea410700411080380240a0036146550140507100000d80260038400040700003070b903980306d03402c01070710982c3d00c0103008003e45054504050010020b60700c540c006204025a0215400d1924010103c0000146500104ca541004100803000a803e140c0c0e000f039001d000645032501d44130080d013400003085000d0056020510002031074100140e00003610342c03100d654a060254844012182043c1c101c1c2d00c045026540c680069444446543c4010b00c0389180080c00a902d4502042225080103016035a95030584040142802d95803140c030009250300c0c0c480003144803003082c2209400941c00540c10f011000303955800060807604103c039400d010492a0341c3d0200c9007040c0313104034590386445003010004140075034002880b050b4140070f012518a980f0203111112101081740c4c000070407821080301da440c00c014110a0143d049845014285101d021006c9200341840c01400c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 304770008 1250 304768758 304768769
    0x32060a06080612010b04110403031101020306010e040f0b030f030d0c0e101b12020303040b0a200a05070203240f090d03020f0403530702060909040c03020103060b04 72
    0x12441c03601e6500800402242507a1100901e45da0f4041c000e102d5151801017192081c0d00f0b54115807a5031660501a005850a52111210764410400c000f4141e03044480c06000300c0302910009507800100031080001d000700c0711210352502c40c440c0003000d4464000020900d45850f144180003190013030f8410b4440c20450703100143d00c00080300181c00110f100d80400300800501489030f803030b06a8207448001d40540790201500068000004001c1406000440c19806c149081c008101002c8a00305c900e8080d103c042d05801440d50004071001520321032410307601c0301d5070020140d0b4244038903000c02c44010f88008045d5005a081c61000a10080401c010a8466803102c1d01504003c1c8039041c08800a41c40209407110803242408040089020040710200c0108489420042c2d4000301100c01c2102221182d0001c0505003e00d08489d00c580c1c071070a0b01848951503101c40d0b00c80380c043c4000b0b881d07805000500d0790441402401c000502c940141014201e82c000c0e2002c010b1592200d000072154465070051 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 304771258 1250 304770008 304770017
    0x4090c050f0a0503100b04090c09090b060a15080603120c010e0601120503031b0409060305011409030a0504120f1e0b09010c08043203070212030414060d32060a06 71
    0x3e028485072031b6003100c0005d040007000007554640c15600c035841c0c04441d4000480700d50341e400300907003040601413041c2d80049003150100c00d030b140b800114080304405501100308204141e000306074070307840400003580400d038554001912014540540c1b40200340321f0083e181203110740c0740009142c020030b41c0c01ca0035158004026603d15a1001c50f800c0040c14a1926a803101004202c00507448505100b0100994818400442d100903140410b40358000060440d1641e40c0040080108054209040383c0480707040c0311480b046c20425081c10100746200c5400503155244480c581c107000349229074a6107160344620050340300398507000310142c22255207404080110b8440c8000c00e001c68601c102c0c0301108884401404143d00c0b100341c8120025a02d11a03910a50707102144903011440c00c0d0707202040900c80b0300019410249400d294035012500100d505000e640001061440b1854a8100e80f082e248001000028007074140c010b60010902e20007072110102180010640ca4600000e9072011541e1320b966 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 304772508 1250 304771258 304771273
    0x807210c1a0c19021207062a0207170708010e07061407050d1b020a1e0506250f0807080d050f090a020613030c0e06090903040e04110f04090c050f0a0503 67
    0x404244000c19200070410b520074400400c00c11507011004004062141d5400307d0540786810740034a5907a5044400231115500c02d1803020f100740c1c0003c1800403502e110f03000d41c1c01c0004400761a0704180f00c61300300f0a019402c048400950a85c00035554040340e02e55600c400c6002501191000540224500101b00d07401101140354988c0c851004054804241d40600b410b40b603250b13000940c0d001c0c0a90000040c510132842a800004000030580001d02e01600c4841c903181d130000c0c0130a43e9a04010312030b454480000c42440600c001100c801490550240e02c8130f40d108183c1c00e100c0c5203030b04440f912001d21400c3c0b50014011611012100d030266417500d00400003840d00740d0801540e03800003020010380d981100310000104011610300c00041010940c0c08205060090900c0940c0038010040302d52503104000c1080002c11101050742d115070441e6400b140c43e07550b400001c0b456000399600b15402418400004244129444030340d04030b880232140b8070b0604030f4000a105000b1428400c0f20f505411114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 304773758 1250 304772508 304772527
    0xf051605031c0c17070c2303031b15151311030403031d030f030f0601020102090d031101060902030c030910051603020304020303090604060f0809070f030807210c1a0c 73
    0x20f03d44545640f103200c0200114120f61940c9405401440082d1118101668100303d80500012180044502104000c829590b50b0b40440d80e20701c41d0754441c6030303080d0700c00c50180c541000520071000b925603040c0401d04a418110074001d85440c012107550710505060590050b07106040c4200028010051016070640c0d4847d10700b980203282032000c889c140292000c0a400c09842030008003010841000c0043d2a820001c0c800340b0103542c01401076042da0700c10088030b510381d036400c101400b0040c1e161400070181d0700744640701c2d4003410751580080342490000c01071140d801c1144000d18802d54080f01203070078840104014405842d01511101c0ca41c0404000b8845134038481c0d001164004d00190850f8a041c10080102d24207a005a11580000b0049151013010681c031013149500070322180001c00c111410803581c48842c9810b4800101226000034440c0c0c1040715500c2c03050f0498030301c9694031464a00084c405801500c1d1110100d58144090800841d90b5106154590203016004072440c00d1080c0c2c0ca = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 304775008 1250 304773758 304773767
    0xa0801090513060e0d030b061810050f12010302100c0b160306030213021c0b060a030504050f060408131a03070e010c0b1317160204020d090f051605031c 67
    0xa400c0d007200b089080803650114009001c2c070082221503d000f081c8403168002c0c02021a101c082d5814800d0104003c443c1000c41007640e00c035281401251300c0c50000840b0601510a8418001e01427407184010034202d4918914058280c101d9001b0b503000c2c1660340441404942d20102060000c0c080683d11000ca91003c2c415200403007403900134100041c01d2500ca0300041d441c60108108207620a40001e00416403010813402028110710380c0c80700b0f00c0a1807644000400d1405903506410405559000040c2400070400a409800071003074113035200ea04003402c01803415800fa084494104903403610004420181e880c2500100d03260003142811515079040c2110f50391a010281d504104406c020780000c40e02c1d0403e05400346c4101210114541035901e001e401c401c500385440000c41500740032501d10030300b041c1858121954111401a5074070255540d40c801003c0c52140906214803059405040040000b002c004912440c00f5460710142d0f500c00f00340e500c3c0200c010352a0700c20140c925118085015 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 304776258 1250 304775008 304775011
    0x305010903080906131b0f030b01090e0f07050d02040b04140108010c0207080705060915031302010905010c0b0609041407030b0f010e0c0f0711150d0608071211060415120b03030a08010905 82
    0x2d855006e06038980d01c9113500030003c0550419901c41d00b19000400c036800310f0303205641c00700044078041c0c011640388102c000e480e908548030701405111102d00c2c048c11582d441e406407400380310003002042020602040098488024022211158684481030a0b80f900000d80902198070340001801458141000d1100c5034102402964000c105034924885180f810000345110350403002122001c1283da0000400e203003803a41c49541804040180340c000b00c0d003070100700c65102c0c01c183c82c0182291035621b4511055034a04039510300c00d00507410b010003082944e50656002d00c11100e1040c0703669803170301e10405182b0340941e00c03412002002c028544440a00704081d2101900480c06000c0482071000402c021050f0040145100040000e111a580c011407080c000a000307010000c00f4080e0400900301e0301c440084901a00d10b171980e024208256460004032005001f08034604024941e01c4d002c00303040e075408081103500c29410325210107414180001600c411800d5035684981c16483d014004008100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 304777508 1250 304776258 304776293
    0x6050105031302040b1206040308160305010b03160e03071203090812030609070507020a0e1f0e070e030309060406050c1c0e210d020303090c0a080d03022101030501090308090613 78
    0x10010070400401c0002d200c1f00384104c1c02911076515074030f0314101d1007080c0802d0906070002d1518120052060007165419203a000c0381d034044030b81c80340c10505016507003103c0010505525204602011941400026084140e18420303152460700917200e07440039880e0103d061600707501c400f080c00000c40e00d140a54480d40c00c8490f6040081c5031007040c2e00801c050800607001944a0b60850302440116040c0c54090100c91191154100c0003a0402030900074061780034004d2410081580e04100065800f80100c892203080104165900d550328900031b05a908055010038482c040c0400000d001a458100c2d40c00d1000c0b603030703140010842c0c00350800c02c03260410308100703580020f80306100c400740c401040f0078124100c07540c0046850307281555500e0b1512007448849406101ca40d00100540b84001541e40000328103828056103441c944c5100080404d800003107840c90a2152380004140141941718a1116010303a03161a9180d4a07083d48540e01c0e802a1280040b0040108661012940c001c41c3d1580162 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 304778758 1250 304777508 304777519
    0x3080304032007140108060906090c0306180f07030c0f0801090f020c0f0a021002070503071203050c06070509030706050a0503040b190207030302040f060801060c2d0f03020106050105031302040b 85
    0x40b81c2c0e01680d02c1c083c081d80003c541d80459a8441c822982c20441d4a5030286003110441406d02d860710100e0107080c4081c015503406000400030800a5444982000030901c0d11084402d035842c0907034a44070983e10a90b80c100120340b074030700207480c51031081d0400d0a4566898603050a01d03464004035400130000c241c0c100c0007070745e828000079a1602c0107000340c0b00019600c2e0020081c0762800c2c010442e001c90b01074030175019036000a40030003168602081b1502294074500c564001c02d401810b05548601c5959a4480640146030400c40c06940203070113010b56603c02c2d81152030326601d840040e1070b144602107404000c40d00034000100091850004c0580c88940c1003c0b50074a080c40421703000c1647c218000403000f09030007060611004030740b401500000e152500d82001c06515205028040c06260407000e044250b50207603160022140c030b91a0440c40140510751017400d80344e4103120a244801c41c100f18015400c05000140c5507101d80c0599004a8024003d0420400c1680c02c01000340500c01c1c020b074014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 304780008 1250 304778758 304778807
    0x3010b06070609020a0506090109031e05161514030c0705101503050f06071b06060f0303030501090507020a17180a030f0302070e0f0403080402030309120c120102040308030403 77
    0x291140300c003800e1824824007000c10b0718021481049902c6195801290145600303129440d5240e0b0300800742000c82c0e4004061640c903520002604102560007440038115104001800484003142e00c2048101c03042c44001402480700003404541c04140140340410308501480820700d0720000d400141805c520550845511620040440f02a070b48203d14511800408120800a1103018040c800f0760051100292007680341140c4040d14104200d0170700e40f03611442800d1903042100710742c4040007410480c1085280b0359581e290050280c2024015020410304050103e4940c07030001654100701035100340300d64264240d44c590240030f81c009007443c24074000741e403c42c05016110226030002441c000d40c0042101c00b12810302a00c2d240700380d0700145c1d81d801d01008014043c40c241041039003180c0c1c54580350300340c1d4641d800024514081c20020b00d0344008481c2e05040c40007000140d81d0300131075040e03500815803001c903003c16080340940e00c0301800d071447c1000081c00091082519005040c824600c69151 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 304781258 1250 304780008 304780031
    0x50d031b05060a0c12110f03181507300e15100801140106080f040c0b12220203100c050408030a080403030f0506030a0209070509062a0703051207020301 67
    0xd107030082d104a043c0c20350301d48004a040f0b80c8030701d100c44d007860420b1040c0071081c030b580b00b150b14074817428101b203441a001001140c00d0309100c203220700f030748140d074401c07242828003002070703040d1590301602d508011503c01d5a407000680e4054642019151500c50b5800c0c0280b86d01b0400800b03090314040c100d00c41d002d0a400c4c8000b00042c0c0e10b4441c021541981c0611440b030800e40e409003100d001c2102341118103215001008480e61100c241d0381d000c016941d540800381c81702e1400c007641d035026801c00303418114046143c1c502c00210104451180e603016100c00c000c0100d422621109111100c4040c1d010b80040a5203036011007140c000651128480c941140f802d42c0d2210101c1c1507070011a0081b0010300b00c5014001030503851300600c411a808101e0801c01030a00000080d59102050300c02405031060380b000610391400b8078162056814007030010340d500c928000b000c40031155051201400516200c0ca03070001c5240004029060340e80c800018044c0140c02c0c01c000b551600326030401c030782c10b40d2103503100182c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 304782508 1250 304781258 304781263
    0x5070c0b060420090a060203040f0b0903241b0c030a0302090d020a08030705070605040b04090b0118121a04020a050904081c020c01050601030e030a0f1202181801050d031b05 76
    0x62803040c02c2203504c40d403030942080f092500d00ea1003034007194018842803280a5803040b01000b02c6000c0500c10365200060b5012034140f60458401001d580103a101942c1c8402c0c0069a0521460b0b0300c601e009101000203100b8200c1e401072a41c0980c8642c010712289280d030703001e40e0042010780030040600036021004e40c000703031403444a034020080d5600046118000c00c201040180f0180941c2e00b061801d160400307a50380f1040c0640c0c032400001039101d04220846900484101000c0c1c0e0390100c419a07200c3d1523140310a000c110600d01112082d80e00441d001a055142d03050a0041e903000f045000c0d00c500e088204040540003403c159500300c810001c0d069800b403a140250011600c1410158491044c0c5c1800d03400c5542c01810f65050604015032040040e0021003101c4500c00f19007407a166034058040d046841012030013500c68844e10020f04152441c0020708040000c1c2400c4500415161004100b43e1124100b071240c25000300000458400290107000c01001195040100c1d5a090000b501c40a2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 304783758 1250 304782508 304782551
    0x240f04020d02190306050306040201030507050c0105180709050606070f02220b01080601020a0c03060f09060234050d08040327031e170702061306050406080a05070c0b0604 75
    0x80c003655001a1011a40c1e512100c083d000c0c00c05400c0c04c019062030000407948a401c01040241010f503200000f440160140c82611144c0c003160b4003c1080f8641701d0001d10628403108090051849080707000142c969950140783d06c110070280049003089043d0340c46071080c0c50b103468100d80c0450001c3d034848072496141c2c2e070005007404940e40454704414400c005003040401612813411904803840f184c000c569004440c104a0703901c00800280c180d004c2a406000300013004000340154000180c54000032030030340034407814100006803280c7c04c1c540d100000e0f8a030840c0d00001041d5030441d0407403402403402105825486400381c01c1110f20b1600303000514000744070594088003083c540000c24420b208007422260484507140c0500c2c15039842d40d440e000110000929030044000c000524202151078440c1548e40d03256500c44421003458981c43c01508540080c080d01c00001c1220b00000c007510b0340c078019180903401d0ba4903290240c3c2095100c910b800c01000380107039045030716501d8a482d90100c441060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 304785008 1250 304783758 304783777
    0x8030a020c1e061b040504111c021207080402061803070b0f031503070609120c05151902030f041a09040504120201050603011e051b03010f0306050f040209070f0201060815090d0206240f0402 83
    0x168bc400021460220a2070040c0c50b080411000408220040e210380c0d040b120031060040050f9280c010020000e80307028101d030481e5100c0000850050103660703909000c1c502580e1680c070f69040300b10400080c155038101ca032050030b00003118504100310000000c1040c01d0700c0ca00a2041c6001140c0b51b202251940e1280c9030303c01c2e00311000040701d43c0c460048440d0f045a43c0c610f407000d1882c1c016601403065080c01280a92502d00150203400c411200c905030440c0d905003000792040c0103500c0c241c03c1000040d2507809922015501380400a405032806100b013240c2e20001100e6401048010410306004210041030340603014a5080c145420032082d401641c02020300003600c41f0384600b145445400d4031000f424010603004a2828440182d58414805501c040c60b03181442140c500928103c2c00340c00070368008099409281c000080c07080060f1750842c4900c43d01d00031543d00001c413103022079581c0412a441050208031061075a0324900ca030000b4540c0c220003d282108466610700014106c1c0d00c10840b1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 304786258 1250 304785008 304785011
    0x30a0b06041214150a0b0a03021002160602030f04030822090608120708040302062a0115061e140d060803071e03050708030a020c1e061b040504111c 65
    0x40908100c0c0348004100700c038030b4220140100800b0101c0186130044041c24035110240c03101c6c00a00d00703407101b241450045800410b20070031142610f43c081c1d184e070a000e041c69401001000d01040541c00041182c0c440c0d0312580003249001e2039074403500d029402c0071000f0303860b054601591104900c08035101d0000b50100c2c2c080090b201d0b151110080c5003078000c802c3c0c3c44d201c95062001d44040740000b400c0c0d0741141c0e01980c0c5a41d41c0c20a985628402d00ea101d4054101c3c0354042c0c481d4464070405600c0001d84264002c90501615202d0406543c8011b62006400500c400a004180d0b1648940221f1410116a000e41828150704c40b00c100103982080d0480300b0b070780d440400c0102c14403050900b9803000c20200789181c0c12070034050f05d004140d44154000a070061400201143c45003005e90304a41580c404241510000e8040c64600d22400704006035408152080c200469020074005004003082002881070742d24240c40c140921000c0c00d180011010140814401a5000d2426841c810700402c04a03c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 304787508 1250 304786258 304786289
    0x2e14030f01080115030c090c0c02060c0c0406060804020310150503030d0f0614010206040b04020a0e0f18161215020313150504080a18050a0801020c240705030a0b0604 73
    0x35030707085134552072010351003107041e050800c040f0340b1075030f450816036400c030b000400c082c04800421781c0c2d503440b1090002d42000000a2400340d80201080040e50b00c041110140200b903592182101c85002c2a0f80107507064005008002d00e54016134072001c281c400c40501e0384444ca98500000b41980c100807028244581c0b00c1c2007540c41d1180900c611400303440b03001541d001c0200b0000000b5900c04008000a000070302010124040d95100003411004006240000e0120700c3e203048400302d000d50a841c561200c4111052800e80400040703a108008443c192510b031451b45030007078007080403ca522056640084a69034018101c065000551007904039080340d58415503d03181000c3c0b0035012400c2c0100151030103003071000203034140c01165901d081514000d514910b4190110404207410b0b40290342c89643d00000040a503019006841711121030070580b40c100b0a00010258000b030400000143da000560000d2680d80c0140302864200122030000101008018085101e039806a0466940c0074440320 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 304788758 1250 304787508 304787519
    0x9110903011107050706050c01090203030706060819050c0f0103291f1409040209102003090906010503180d0c21020a0201032f03010509062e14030f01 66
    0x12041032140380e10380c45180400c00e890301c0351a0505c41c01030800f000030010300e00c0903e50003508004401c80d0018243d076030f01c9542d49400c90061000b4071800d041c0340a0100f080601288100203103140ca034000c1c002e130031008110001c002c07514000c90345842c1403569540c0a00360718070700000071003500d01c04d4609813145441080c00b00090a070380d442d0701ca0170141000d0301400301203501c010f010551a10840302551104045400140a801100c040c05d0b0042c0c9900002051140d00c000c4824031364405081006075980e203101541d1700c82c0328121620343c0080300100071030b000f075204100950b8010348030701d001d200b141142c0c6051420304110219080000d8000c6200d40c0a1180120540040d9094501014440c00d0341c410065180c4140c20b0000c0e05240d0303516130b01c202041807400368090480741408201d03151903c002404500ba0028003c0c1402008a0000a40340c0d00f000c400d44000983c060003906006240118521804020303403015008101492445080c0d56107a00f014501818011002005560400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 304790008 1250 304788758 304788761
    0x60612051507171e01080316020103110c01020a030606082a0d021309020c0c010306080a0236150402040b030109090609020d060f0c09050f060c030c0607020a15060509060d05070911090301 82
    0x11b030000e6a10345c10402c1130000e080c0418845802050342824046040d200305c43e9103060030f009460704500507500014440000c2c607416071009040d60703a01d0310356600945481d803050095690104207151001084801110400b00e82c07005441c0c0030f02c203180c000d403a140f1080213044591000c1d03802810680d4010940c00c1e152101400f41c0070341c200c4c082c84c041042600c0d190340a0b40d10083c0d000c001e8091044480b00312000545090400e210080f41d40b886070a400010a945080460840d5081d02d1403510352031024262909000300c41c103e5001d00740507801c40c0d08001d40302000340442c110498070280d584e4540d00050f242c800d801c0e25014050714000903011507496400050f5441d0119030f904000fa154002d009039500c0100c42150a4000c4e00c3c0e0a854003500c0324914a1072050301078040c1e651141c03e04001600b0750009111780da0714400d083c00e0000c03041a0080406441e549d014695110320400c000849a0030412000c0800c0340c0200b04030b820031690381d460038007201c00d014098108420000341d801e010341002d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 304791258 1250 304790008 304790011
    0xe03040803180f0a090207031701120b060603014b210503040b0702060c0f0705010f02010b030607031a090106090f06020f0604122a060612051507171e 66
    0x980e03c00000c02084000100754100d98002c03043c0e003980c081010020725129118400018042d0b00c00410556104d10b00400081100ea004075030b448001000500d00d41007032420323a412203040b21004105030305d460000ea60316003681002402034480d1594109103120a01d00802104610101628aa00d0070b241060a01215580050540c041d000c040340000520002c1110211031001000d142c582866100003030503403040b200c91400c80d00c68080400c240c4600032900030119502600d03a911360011a020903820307912034024081e4150852400035441702c0c000e802aa9007045c9092046d0f404c0c50200e0001400c400084c0c01c244001040440c044c0314180c07054a80f400a418a03000410b40048401100c1d030f030b0307508010300c000c003540c18401c2c5ca558550300841022103940c03000f650960070300c40310407403112014031482c074165403440c105a000201c95601d243c4403d0240d41001c00340041000d0f0f042d29450441000c2c080400f04103054001c00150203d820030580600c105100c07003000c3c9041c813210310519510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 304792508 1250 304791258 304791307
    0x2709030302131410030c1107090b040b1009050d080f0a030e0d05040b040b18030709020a0e090606121008010e071d060a0e071202030c120709080a0b0a0e03040803 71
    0x40c020903e00d140da648420050f00d80994600807540c0445010100d40180e09440244054400d02a003c20b06002540020b6000e02050b0380801c00002140c3c100300d60001c0030f003034a00110344a03620038022814900c018041c801d019580440c41c01c082840aa4881c0e0b0118904100080d03582d20f4034400c046003401414045102403610606150401090f245a8800e0f0b11035910f446800288400201c004204804000400103060303510349071360390401d0700c00381d442921100001201c0c0504220f00e032400d001214020345010344414100720603c06c0801e03200d8030241445894004c0d6500c0002c40f0b10f02401402480400d61014160301072502048000b00c071212059512001065410081d50713440340c42c420804c07036842c1c1070840c000740c940c04da041e18041c4101d602d60759414000030401092010b01c41c0104a06040b0184141850ba590501290020f0490003260704641010381410007158050070300f1908140201400200240c1500c6514910b5210f68403026140d0404140c16900d203d006542c108241c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 304793758 1250 304792508 304792529
    0x12080702061f0608040c0b0313030e032a030f010e0d090e01060806100504050d0305030402030f0106031e0c1809030215010302030a0803090115030804150c0b01270903030213 76
    0x2407140c44100c810068001c0340100408640000d080c0300746c1900501c01801003e40881d1340e4205a00882c1e40d800c00180182c2c0801c05061113100d2505002070500100c1c01c1440104481507800c01d10702d416440086c0c01243c0c1031042004042a11000384242c00641e03003504001c2000340c11010020f08202c040e41d0090100300c0030500100300d043e402515990f8054002c40d0a50207803021f4100980301ea004541180f81c2040c07111102c2020550007400540c06240210216113000130101811402c0c4e414601008041c803040c104605549011074079448036980c821003401c001d4548900c0c18140600510300452407054440302500103054050150413503c03421107c02115239811600482d90f07130041c1e51303001400c1c10307030000001f03984400a521410080f0b140d452015481580d03400c0101c0b0302d801500030344c12029414480041d60750300070012200060780c00942000300d43e2a01004140351420820f8140151a04405901d0b40c00110701c9102c5156209460058035482c5405081c020320176180c1100300e005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 304795008 1250 304793758 304793791
    0x106020c0108130b070c050102340f0602180301051e1321030b13090203010f09240e16060206010b0405011211300a021e0a0c1208070206 60
    0x6801e2410340d030f05240c10038100c21041d02c0700042250700f0003076084013400c00c3d440801c0f150010001516810b0040c01c2c14150404014140c100456400c00400c40c01401c031511600c901c800900107401038010f600608030041c5d011a4481c002ca0309651040303c00a04100352402c001c5003a990038050702d9004030b04c4d04d034429418000c503074801040c9540712065001e16440c2400302d01900e81719070018050000b024022500c0203468003522009403c48400403032080d400d10910501c6040548140b0103150741202e201e226168029044504000c2400442c0003010340300e0300340940507070b07042080034403002081d52910246440c0c40b00003801c1070410303000241b85e02c2e0f08120800450707a100f0300b58011304a883c400050703445400066051329200300e161159460102654102d241c14050071018400c02c11120202d000e541d038821044124480c20801c01100b0000141015422107540080c2c0070b001c1e854100011142e14945441106088505041000a20140411045c142c0c1401129080003000c254207034038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 304796258 1250 304795008 304795021
    0x1a090a0603080d020309030d060b03070807110a06151e090b04020a14090406080d03061a04150804030309080304080a020c03010c08060409020d0c080303010501021c02070b0a03140f0106020c0108 85
    0xa2041100304000c0f5500800031607881642402281d41e0940b84403010020365031744002d2000740d504215020408a83c2840005140358014010a0a04c0c414080544061710301555400e00810f000440f17200d0510f882800030a130032419100e101c46004000000c80c42003031070840e1200613200320280403400750380103101c032111b416040f1005da500071000c3c06480b91900e81000128006010f5507002d100315200b0110f03400b403240c0d0103500c8030b81070f0350828031848800b4807007483c45282c5210340c2c8074030400b46c4141c1904031044e903c0740c2c4440b5013003482803078081510b40d0207031240201900280c4040d2150f240003d00045201e8040110790b25580c815402800001c2d0901d0000d008004020841801940c80743d401c00c0031503a4609032803555a90000e00c1c00301c1142c0701c00c149654bd400074000c842c003500c0b9019034500c1d803c0c1c151454030500807213a0b000f400340500348800502a5041990f00d40140354a520b04000058042c034625482000c40b050342508541c076082c0d0003813410150484c4181889000001d0191 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 304797508 1250 304796258 304796273
    0xc1401020c19150504060f0c030e0c06250302010b01030b0306040b0f06040902090a0501030203010e1203221208040605011703090d02120d02011a0604060f1206091a090a0603 76
    0xb904500c40b600d0440506070a100441c0c4010001c640c400c50710300410841044440c0e4048200c82c1a008010800b01c518184107900f05c5682d22084903060b480402c14008601d01400180542c10070f24090a007031903c92109204c110024010840150751120300464041d43d00d84103a405901045000b09a07500301600c2e81e1401860103000c400b14081028002115030f20303031f81c01200d107099000d00310341c14900d031040403a00100020f0100728440d50030301d030341c010b010031001413200d1602941242403803864039440114040c3c650f00c0d041c2d0f581c82d03180c491400301c041007605001036144200c40d12906120328141c41c1c90021540140c1242c8992454810031300201000041510003900e815105015040b20500001380c251100c0c10b510200d91040002c50040f00b0360640202030388140d507289144121804504100c4140110b028100c00a10301c10411098644650300078513031000d01e00e200248250700d94001900303603040180d104002d031a120004405509041c1c8401c1d03840660b542d800c1120a0850740e03a00d8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 304798758 1250 304797508 304797523
    0x70201150b091216030309030b1317070c0e040501020d050907060203180301060e160801080a11010e01090806160e191215060321021c18080d0c1401020c 67
    0xd004003440110445018010402c01e204d118400580c00c1519a980c40d005000c002d16000c11a01d20703002c0d01c0030603960702031108610801c9030301c540807005180009ca43c1e5440780c1c104660545640c1014100041e1180000040c5801345020344001340e030b92100100780006442c1c0207009903005520a07001000500c2d07020040e100704444802508401e8455400041c1c0540501d401440d108203040c0d0910404062545ca60b03090708100b620340c4503950ba6035030381c00d41e103402007034001810740c901c0200c000d1060b41c441c0540080003d414100a03203240c1c0c0380c0099525191080f211040c54401c42c04801721400c4c1c0000425800800480c0d40c549103000e0005c2d060070740030203449031140e105900d81c4104c04200392025107610210b07aa01c401c0046d540d8174100410b582c010514400d4030298540c0300344011602c0491000c000600161801000701d01086044400d5800000b4800119100d040b01003280700050100c081114415030750228400c5042c24415200403071851608000ea204000e4210340540100d5841c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 304800008 1250 304798758 304798777
    0x6010e07030e031308030a230418091208100e0103050d0e0102120c03120a050405061501210c021204030b010b090f18072006040803070521070201150b 66
    0x2054401219000c03d15500401401c000118042000420121400800b501601d1070541d520003c1d0095072420000082002407480c1ca101010003082c0001ca46100020300a4868403000142d40755413030700c9250307261000b8000303080010b01da2804e0006000a210703c050242680721411501945980c0d103c0b55148004441079046c85440283c8501c40d80c0244102003258101004d0a9a02e052030040681c807640042400a03030045503202041444190b0311440c0c2c4140d0344200105525100c02aa041002e1036503803142d8104020003040c142d840701c1000e240c500034402c045011807a1403403284080d0a081844c29812015030041c031003000402d02038546a41103c0760001410380d228002404110000c9110349540d400c4455042d210b10b8401040c02500d100d000c5130394070b54105201140420340b2a104010b41c100302030340301802140102c2c4050006641000e07031810207501d1300758095401c0446105103a100c0710444411020000a281c082c042c6d0b0025860102145603030304d0901030001c02501901442 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 304801258 1250 304800008 304800011
    0x304050d0f03180306140703050412080411060412050c0301050405030d0b03070b041e1707180e060c0c0f01060f290c0106180606020c1513060f1106010e0703 69
    0x302001d01d405811800984980100c8030402581c1301e043c002c000d01003e0701404a030ba40d8620018514070b129200e2280030381e40c01100c0e0042004800350445100c08054030694500301415001091540e07104000c0000304074088000d568605e403130500170300301282416128082d13410901000001000801120701e10400c0000c0000d00600c036802191503c00643c01500c0280b10001e400300e0030030850364420078188810300300490707d070f9161090300703010300300c3c08494000d641c0c09414248090ba102d544150032401050310000380d406400c42c000c174a04403040d00c00ba140b58400080158010300240702c0382401e404440c00038002145005034000c2d1641d401d00c0390818102e003818813145169030940004569901124102d80c4515a4007070f900c1c003c010f1449400702c000032801480f840201203000e40700071a031030f40e00503101c015041002e20800143d003020110b03064208002c0300c1030a42c1e603455600060a0139540c0c0001d400c41b904000f50184500f0040c116565000900400c542d042035424039500520a1a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 304802508 1250 304801258 304801283
    0x7110607060b19031b05090c0c0307020d141009200d020a0e1812030c07020d080f0310090e060105040e0114040f2f100507080d09020a06020304050d 65
    0x1440710040114585050b031207400c0800424090018410140981e03002e484540402c140d98502207090b204c45101c0e4603084401b00c800250021400302c080c210141c1644250391403ca110f43c00100308140e030240881c0d10300341048102000710350411400485100444040280c03810941301d940018150066009030080020601038080e190b098002c3d541550281c482c50155840e02e0a070301481c0c2d0304540c3c0b5010504079110040010000003034003850602c2c29070341303140785071038480c4060600c0d8080702d003d0340c201b4a019500030010b1010350081885c907145241c030300c2e01e9013003002d402003142c41142d2180b03007494280641c050070512b0110301e80d411160121400603003e020f130017480e80544010203104882c3e940390020007003404205284501d00c01d119000312251030072508030f4083d000407400b048140007880a103229400b810105c003898140a000e0034028148005a1355024159000840c0042c030123485000240442c01c0c1030364001e01030100b50014504240c1420b02162009140f44d50150007105240e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 304803758 1250 304802508 304802513
    0x30123011b06050f060f0a09050606040e0c0307020105010906140907030612030201021909030b010308091818070b0408031204080706060305030c061e04120207050405091b0607110607 80
    0x107062803941c101e00103015000700d05041000040004980e0604840300090010341350b86052003600107101d400600c009034541c141640040104402000250804020040401e20100a84145102d095807101d40c6980340b0302501e000707003510710681c00000c2580c1010014000e5176541c0700d044000c2a401c0c1c80c021165540c0c810110080d0180da882000702c0000b10340c0d08000d040d030640060651500d04802d4003880d00c2a00000c07910800c041c84090101800e40340140b00080d0204020401010003d0500074035a85c021814441444207236042d44201c10750070105060303d07600340308401c01085000111070800307240c59502e82d03c0c3c2c42600c5101010b6a0742200140070400d804096802d504d4002a00308509500e925100303a40368000c02400d0014800c00c0b00144004000d01c1c040200d52210810a41503529140d444108802c0c8140c2c0030700550207216004207064071584252803040b50000c008000c41c019058100f446594a4070629024a40400c0210003007507104d41c000c40d10504c1034a00540e80c010a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 304805008 1250 304803758 304803767
    0xb0304080315190806010e0105030d050f070206030703090327060c140114250c030509030f0d0207230901030f021305010e1506030415150807090603031403012301 71
    0x880000f58002d450181407000031a00c1001c000a44160741d0403a445a601e81c000400c5034982481280d074541c2c494040b403411030f481400138003507032024440d030141008030643c0000c040e9042241c80f8000242c1d64800201810b60080c2505451012524100000e4200002000500250780204070070f016001a2110411034200130300c1038180c0c1a10700030040c003104540c9801e140c2d08d003a0b686203015402d80f0041081d214004003240e8013441191107160031910155415602d81d00841d100980c1405408dd100101c500240140312a0070155400b6008040c209003090303a048070048500c111211081340300221984501e43c3e00d0b41900e4004078680052f4540d4400500080e407500c5039000014144000055a00910502c9901550340840071a500390a00c00034004180411907000e01041c09104980401400e554849000401100e410502c2103482e510500e14040345030340304540081da540c0d001c2042c0355114041c0755a040c4102d11035440d40d4504403400300002c0041e158080b030114401d00100b0941c0c000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 304806258 1250 304805008 304805041
    0x10050a021c020a0c14030105010b0a0905040b010e09070804030219020f21030406020d0e100c0638090105030d020304270e0318150d0905010902031e0d0503010b03040803 74
    0x1303805040c8103038a07040c084078964004600d9900a6080034004a9541980f809980b803440003030360344003482490b250801014207100729519062200480e0b8a0100307842d0881c1e114424001500c1c0d01c42c260a091400a1030410148415078070043c900c55060016550503201d18a54042180c0b54407a160404940f00c58408000301040c2403440002030006851f0b8010414031500f2081d500c8819602498105001c0340e01a948040c400254000074020005007465000f98400318001c21a0f103104010004503a101405a510000b1030bd10051001280c40c6451032030940500001d8000c3c4c010a450030801940d240154002c0029503200f140e052150849408440711300d000c498503041c400340a11500c171a0b1680d01c41050342015054401c880b5046040c220f40c80b40d080b075a0030030703d645030180c2106594014000070300101c41c0342d502c0741e208c030016075010490b400d4511040030320354000d1044105010305c1d0581511642090000505c010021854501c0030780340d002d60410055aa40c3c0c2d0b42c05254030800740f5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 304807508 1250 304806258 304806263
    0x414040b010b180607081b060405060a02130b07050c030d09050f03010e060f4c3008071103060f061c0321051e13020103090807170910050a021c020a 65
    0x21009a0f10541440015080c0c2c001c900800654041d330b1641301400b02a4424100c202c400d43c50090410441d040712280106001c034010000c0e109035030a0540003d0500600035100320004803080c006000030300e001d01c00382003c0c101c110020000442c1ca01e0b1500d4a50034000c081d802d4007560180000c3c0015400d15801d850491044044481c107414221a410800302010b140b44030340d003030b042c0800c103210361314907601055884000240000303040500f4020f0b43c440206000e10981c0211211050006802e003002e003003070900c1240d40740403181b22036003418036018008060100900e02801803010580300d502c10700460200c80e00000108a00c070703040640301020020303c09001160700d900c0828018059a201d43e000b00c9100a00da4680809107119600c0c2c180192542100b40c0b0151044c240150b009038007100c481d9209224840c141049a1110b8600750710004c2c0901d090000000c0801c03141c5887d01c2c041c803071041c01381030007800d03d031000c0002590303202228408181c0e0502500340d44648c40c0204103880540f903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 304808758 1250 304807508 304807537
    0x1030908040b030705030106030b04090b040b09070e100924061d1c050c010c03120507030e060a020403060b0a0b16020307051504090606021f0b0d020414040b010b18060708 75
    0x4c10744d01c0101154000d100d0640007a1a003903210109180602400f0b8086401c403d40c1c1d04951110744541182c000003030a440f0b001c0c45600b4001445c1c5100a080314418403121140401d20792908644405841d000c0805050500c143d00c0c0000090790003984210644811b490158030000740c240740d10341c0000403541d8903684440b504010648540d2200040001c0c24816800e82d442e0740400b20054030500307907544e8001e0100c0c009004840304414258400e6901059500e00490001c4c40740b540c00741000c4003070350000301c46500090b0502c140324240c01400b4160405403000d41280e864400001511b0140d10100380141032421030f00001d643c1c08000100292000030048010ba4090700050111a8044c0c480d401641c4e0a06000041090001c90b21414800383d1400000d00e00c402c403020000180f010954195000705101c00100c056204c0d4031480d01012a502c00b84403050900f03040202046105134480907030700104008540410040c2d20006110344425501161126801d190041d240c1c05188160f02000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 304810008 1250 304808758 304808761
    0xa0602070e0a0213141305060d080c0705150a080c040b0f071a0a270b070c030212120a0e0607050a0c050703080310050112110306150706110d06140d0201030908040b03 73
    0x20301300001713125101c50049804114150360202c0c030b1000d41d141210350561280020108001180070140103010085113a815142c0450f01e8a00003200d904907030321544041c44c004038052f51810b800441494000842d260024100340c5051481c00243c8210f1410500c00000400c1c8201044a804900e4990326800341b140c0c807184c6451007506004003989003211510120b004107410210080128604005401075440d1495a50f00740e8203450820b101d003c1201107104400c00f012141055401a200302481442c40c0009424040303105030607101c00e881548490380040301803150b0030b6004030440340503c4140c00d0066103100c280c1802c0341001075990014012190000030000c0d200d001c0d010320015101c0c00d803034030800201c4a01c8000226010190302940d102e00802c0840e915181081c283c04141ea0b02525461900196540300000d41d860000d4040c034445000c40e401141c422540603040c02303030844402114401030410b00140d0348400b0000064145569640c10f00d09101c000d6007180d0252401c1200e003580c9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 304811258 1250 304810008 304810019
    0xd1b0f081005060f19021b0405040b0601110304091e0b041b200106030609051c0c02130f090b0a050106050a1215080304080f1b0609040515040f050103020f0a0602070e0a0213 76
    0x340c9480c500a51f0300b107202c1d80d2001c402071905200d046d000300e401c03040b1101d0170744c0c421005540c280341680024409120a00001488004501a1502d035111750543e200c1c0001100c03030040d080e10344002c0d050344142d007000f0546204002c000b40c000e9110340585026036030b64003288040d001d04c2c420418604095400c100c0080140038003174000f0180c0511841c00c0740c180c2107800d10f007540a140384038440e100040242c050f450251a140e00d0b0080c0c011307081c101c006401100403c40d8400c840020f074080b2510884c010810440d2601c42c881e0318010310040c1400c03854040e4005008010b000114103409140780d075140d12400400300d034040103001c4c003030400881e075807161282402030b501c1c040805c66003020300c45c8035202818811000507003141c14602a01182c20f02d1116130800c0b015040040c00c21006900c421003c1c400d6680318090803520720207503000010654154014050000d09a228841c014240c10078200002580000c80104179103845042c0149a101d00b200080139214190700405c601040c4e00000c140b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 304812508 1250 304811258 304811263
    0xf1504020409230c09100f17070e03011109030c010c0609050d0c1101050906120a0b13060612020a0504061b05030a090602010b01030c0f0f03020d1b0f081005060f1902 73
    0xc01c0010600c0c560780540e152040c59a90b40f18110805030000d5241108800260085081c69661f03500c50820700155000c640030000558170490f00a030000d02d0800c0341104a050a1280c03154141e8400c8407603207080321520100755100d41900c02c01c2e04000244400d101401242d600c084d080c194400c00390b40d681c00c840790b0000d1080c610460300b618920b45a0545403910341c0030748201e940c1c000300a402e007070510303000e0382c80e910f514107008142d1b604554442c01c118101e036a03072401d031080c11000c0d144000359803410900000c01181e210b016100300540f0401c10aa140340e000070a440850780c180c0303440d914640340c004a0341c01c88000300e400100b440c80b020688160380758001c6031490541b01d84c0d5000f007100034519070044094030150f22040c00820300400c00d80020a2180e00b4425000e042d9050245c036041111601c40700700c41220080020301c0a50840502545510950850400507a80750403501c60410040100b450035592107032a04c55940012014810140a8182e41c0302da4001602070303402d175603404800794 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 304813758 1250 304812508 304812551
    0x302040f0212010e010302220b03011104080f06010302060403111302071101080601211d07090603020a050d050c040c12020c07032105090d030504030c03050c0405010902030f1504020409 81
    0x882d00000209a42d6110341800f4102d9400030200640b0b480c1682d10480e20601c00d495150017144c45a61503002c0d910b0900428065914001c01555220b25046101d800c04440304c0451920360000d800410159031650191000d41c0d0f000ba80d00981c503500a40020185a5650080340e000c4e0300208181051003280c1c1840c1d100c40c402a00d03101125980d18004582c40710a034100e8a0028180c440450750002d540d0740a8000755002c41543e5004034409030003949440402c0d4810600d541d00c0d18024011410808420030090000751741120100c040303942c3d42d680750100405e840307014590b600e01d8440d109229507400d80b48841030b4042150b503001c12114107a180d070700034001682c1561042c04c0d001c5402d0103e14482c5240f001c2d030350f03030341d400c08080038100810f8075000203042d41041802d01c400310120b0122100c41d0000c502c20401009440f20303c10a00040d0b81050380700c0c2c1640d0707105104110b141401480d0096000a000641c1d4207a4440301d00007074002d014942000142c1e619121845601d03008076084d24 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 304815008 1250 304813758 304813777
    0x9240b0903011b021e1617160f0603200f07030e090c0702093402010e0c0a0302010302030604090c300321020705100506240a12060302040f02 62
    0x3840b1481840ea08002110002540b20006074802040701c9042a04000c00d14100b0625805a44040510703507101d100c58043c5400000b5061001d090f0291404d004021074413600f0310780c108c51201686042e181b0b01d11b8200714070030785080c0358440d64402c44200d0500d80801d1022400400240c443c40000c03008a1280c1240000f180880c007060b07480130280c9000640144220035071001c89240010660912205400140c48038031000c00c05d01c4002160400c880515038416020a440780b110150b1440013400d56450b03100290454108105180302c0745c5600600c001501e0702801c0c050790740d8994001007130040120400260920000500205030010460104080309060300101d0340d0f0700c694858000c8500d2100702d80100403580c003101e803200107500001905d14041400500500307000ca10f44405040c04034035840075500d40ea840c010003140c0c1c503025041d6240e00b8400c0a9051082c14120361081003803140740742c00e1081c0940c02910351b010860130780200004d59030142090080c070494440c00c001135003109001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 304816258 1250 304815008 304815011
    0x4050a050103020a140301090503160b18030a0f020c0315011e0b0405010309030c0f06140717010911070c1503052a0904090218010e010f050a09240b090301 68
    0x45848200203004440c1a250014440140c861034a9403240303440410b640901d41554841151001062084c000740c494070000c2c0003212907801c25494500c62800008010085000505044040d0580700006441d1522403d040034070f68940c0d1514160314245180f0403850341403003910000d044100111036514100c4005840440344081c15001c0e40000814600850420003014002007184d907111b604491411800790411908070400d0391210805450500710070b40d81d280c0c17588407803180000301c2c41c940da41c499028500022072401d000340e0908600010b10807a1003452b142d409001c00d01550300304072a45503500c074041050650b55181542c0e40203a0410500b004285842c0c0010801402c200542d0a41c22035951290b0719035113520102403850700034900300d54009607209540401030312a002550440d103144810b800480d8034101805114180581114180f030405c418100a0703502c9000b446000d40300b42c1c4a0203d0a060700030020001d10b0071890803920022440788000448a058000800e10544141c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 304817508 1250 304816258 304816261
    0x18120c050f0a0f0b1314010501030b01051c0b1b0a0e03060106140403030c150c050910030b01020c060306180f0a0b0411091c020a06050d062102090907081b0405 70
    0x401d600c80580810241c1110f9000c4042400103201c96003140d40140c0440000c81e900c09540c40e00d0480072005481d130b1000d80c0d9124018814481381c00c0c0402d0040c40c1c01c85001325020300c00054101034081d80138008040c0100c81020941a40b07401d40c0c680040d0000020440d211481400c008004030701c1c08460b0b41c002d005e09070000c035105100b94038800c001c82000c03086919040c13556804480300c174114082aa00c0402e030780302004981d02640501922420300e0f81d11561034030360950810586184106444050628111044400d40d07004280c408108108444542e125901e1601103003a002070701000d80c100d800c16204001022504500303650080d030041c0010000c3c1d5080c0b1040c8000c5440b249110304032180280410009840c190006200b00b01c0743c0c0c0740b08440b040c0c4642c042145111560408c0001c101d000c034444030106010711462000380403400c00301c0d030320035a9201e202003510070129005c3d000e0440c0c9000115450420494000141048801c076071910849000181c0d05d15480b04659208904050 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 304818758 1250 304817508 304817533
    0x6130f02070b010806010f031506051302030906070c0b06040f020d020d09050f03032202040e070803360f0109030f0f140303100b160f0c1401021f18120c05 68
    0x900171303069504c00030404030210b007140ca525803403031011000740d64090340b00c5a000c034a40d180c591001600c1d00311400c016840341440320f502800c220b0010018010044080340c21008203a601d01c03200d800403010307500003072481036144440019210351080d14030480c3c000141c000030b5031815400584014040d41c1a10201e801c12542039031031388025900b900768500c000510034991f81c0f5400d41400b113140b00810000d1502d880c40f942c5c030304200d11940a1841e0340c00100e0080c083c100d050b24088201c10311340c1082d20100c5041100e85100c403014199080c01030050095240309030b4000d00c46140a10382015001002510902c0c01101890031800101d6035801440030300f00c80094000705490003014040c0000682d103050000c6452250400312140b0f5095402803041740102d022040e035202860301503400c2c008414105580140c0c2c01c245603203400d04561204c81150f400c40e40b20b980a482d070620070003001c680e913407240303010800124624801401150038100d00d06641c680003ea05066944250300740d9401d1850748 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 304820008 1250 304818758 304818763
    0x10609050607030c0336050a0602010606122309061b0c0a020906010201110f0301151b1122020c060105040b2101060b0415020609060c040e06130f02070b0108 69
    0xc2d6000f804100800350410000b0f000b1002c80200d0481560f00d011100e005840d500f0a08440e0301001114101409042c801418044203407006441c0c0d0307000900040e40b0b0144000c1445101524883c0304507511b410408411004038503080c9003948010b40c02043d41411048503458407001e440e03011441102c4001003450b03618a800b560300014030750014160140041e001e001104100820f418115561554a5408d030f80034130002c0d007400850340c0d03449600d960401e0302194011040e2a900310070300c140c60002202e20080c8402d15818a0352101042d2240e10905012074001241800401501c010200306108101c16aa0180100340012800c9411a03640c88051004468020041d035800034011025400c0b00c28107040003007602e907074101c00040c2055a0b1292004260801e411a00d40c00fa2100c504040d411390421100e500401000040c00503030424031300840c10781c8111b00c516140f164040c8006011907513000703103010b00d50f110100b0520540c0c0035281810001c0d449410100c3c0c2c8480a50000f04001000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 304821258 1250 304820008 304820017
    0x201e030d060f0e070f030e030310060801170601061412150f1e0f0609090103050d080c0a020303070f02010b0406030813080105010b09062a0a120804051203090106030f0b0106090506 79
    0xc0011601d0b81350483c00721080300308041604241034440c00c00901d1050308000542c42111b2003d442d8214908081e001406008180c3c44107907500300d4281c41c240b0070240803071100d0442e1030303d040070302c83c165a40001142d10300a0700201e4183c11501803c00a07800203080c02d969582400b1118062180182010440c1d50f80091400e86c0d01d00700248403500c50381c280b5849000b19008001c002d2410030b95203500050111509800454454100b0b168013100c490308600e080c0c0d086520603108504084000da4005e5076400010004004c0010f5208c42c000514000e5000150b0398a001d0000c2c04840c0e180d050031804c95010700c42d0780c0c03501401c0e00340c0050811410311805041e5110300a18070b242a1865042104503042980310740740c2d4000035042c0304a0900c003580740000e0070300c10001030649005107060004007143c0805200c001d0040100400000030b00100700159000d00003200349807661922a03841e401404150001089050ba08401d44d0510800300401412100f8a5031110740498484047c00558000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 304822508 1250 304821258 304821269
    0xa08030c0d03020a0c0602041214071202060a171503250e090c0a0806040213090807060905030f04080705120703030c0803150904080a0e060406201e030d060f 69
    0x1c000c0412000d03911940041104082c64a00318081401a40310341040782d0050b40080408039840803150200006141c4c20804400710710080c200280ca000034000e9484161140244211000a405ca03141400740c280d5410640e001c00c001040d038904a001c0e8442c403010000b295200e44602203401a000035420040b42c090f4102c480b08403142031a2010700c1c01000b40280c901e00450142c03079001040c40c2c9070255114020f00b107600040c903803400d007801031044489103070b9500c01850342422450300105020500f11038401e0703440400002d6640e41814580c1c214040c1e2042c030504180b000400103442e8400042c070005907030080303407a407040c588110701a6546007413501c0000d020440c146800804556584042c60b0320541c44c105402012207018001130350314004031400c9824160210f0b5400701d00d98030400c084081d142c180d9500d071415061081c0074102403462064900c0e500c02d900410101110240300c040c218812660b00f40c4100071800110039100e4206220000c03042e032510b10005000802264045c04036038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 304823758 1250 304822508 304822513
    0x290414131b0302130306090308010f0504020301050603040209271f06050f1507020a0608190e0c12010e030d0603030f0c0206120408070b0c090f192c0906060a08030c 72
    0xa0000e102034000c0e42141c04000713800e001c4054000042201409814402403203540c9242040d81071110b0101001441e4002d00d0040748180014001a00c1d00d404481c0c02a80444100429903141d660f0301000150204a07014030380d9030ba038010107400100103104410701e5110142c92020008030ba070703007800700e407120f00c540c540c01038848494503071900b4041c0c070604400245032040380c540906034000c42e26402e04d5900c0080011031201c10446842c264024a11102d00100424011441081c060a070381e01c10031207003140710704900310106201c9203003548010391000c06102541d803642000c1071500010115848140c021803003400000750100d108142200256500400381400d0941d17140d4140ca41600052080707404010030001e03c40401c21040030b00e44155a0100101d5a0b84268030070f0002c1e0f24a030f080c840703010b0f0251003141c04451004000741000c0c1c840032015030840705000c407000050000d40318482c030180c140e04028009004004200c50f842684251503211803160b81c5d07004c0c0c5650f48514085440e164 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 304825008 1250 304823758 304823801
    0x5030f040807082101091d060606030a090c0b12010e070c031d0301021c0b1005120a0219020724020a0b060f0a080f15040c29041413 58
    0x503454002424055000382a601c1c20064210342d1405641019205180140c0c10300b0f00400001410380980c01404100d440d0521f80710f010144c5440e92044080c1115100789030100000350246c02039445420b410303400c143c4458595507076285185056012040c0511300025810010900c21044140c083c050403440e0745203480401107440c100c40380030301c110f030400d0206000d66004c6880d6400b400680158205010a40801f2041c4c614810846031003d14850050540445058007250010706564505c0c166030421000381e500e040e13425000303102d5001c40c14092198808100c680917400100201a52001c0101501c0c0c2140c0400074101440c401d1080401a401170316000009000f0a4110750081c802928081800a08500180844e807043d0032403da180d00484034140b40020400945000100c500c03504440d44c101a21400f03120f0320326000d80c04e0780b903520342c86404458100941e18040e18109520050319580c844000e0035404890300021403185105291000d440724191144c1c50440da0b18200a1201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 304826258 1250 304825008 304825013
    0x6050105030a0207060603020a14040606030c02030d090c050301050c190207120201050924070b0f04021021020304120806031501092a030203010509160801061b15050106030b0105030f04 81
    0x1960104c40119211070300e5160010050700c41c100c1480180282e14110b42e040c24451060000701c7d0380e20b81c0608101801c1182e10100d083d00071040362044480003d001c00c94240f02d082c0090b051604e0f41c0a03030341542c60101000300701d0091030080c01c0b03e2850590610901d14030114100c2c0d0f100719034080d01d00c40e0744000c0501c10066014000400e860390740a8071103103c510901042c1c0c801014190742618602e003001a085013006060000a0340c0f00c0301c002c3d0b8070581803c20ba0080341901c1940c01c441400d01113096200c40d401e01104e0104400da81b40079106540d41c3c0340915000500d1410081d03400c02041005012818070715000c90710440075840d000d4500c215a10340042031020348001c3c0000450818080c82642418001c884200540305890720701503503070351400b000c0c4468000010111850300d608420000c0120380e010010740e0444400380381c5030010400440c1c0e500030421403000f00600002203540d8072142c040064014030b04075038094804010452550005440c14842207070412489030800000400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 304827508 1250 304826258 304826261
    0x250605040e0a051801050c09040605150d09050313030507050108010b0a081603020d02161122021305060c060901050a020f1621090305101e0c050c03040308071506050105030a 76
    0xc0c84100807070101820301d40c850071306007125010f4410039411840050052038a05260003503900503e808d50f0103208007101a088440780c1c2c098101003010240e2510720754802e1001c00c009862071003d80c4035940e09047e56900c0e00319940e588a00c01d690105000e90b00026451800c107044c0e602c01903c60708c0c5c0e103450f80e40e21b0507611908440310301c580051590030700c1080c2003504c80b4070140c40da03084458002c882e108003e003000141c02d400d05001c0c0d445901510308140d0340410707c41c114881207184a1000d62500c2044070201c0c2d11034034540006410400104070f90004900004400b80100000c00080141d500d07184100001c0c4d100700c20003003003440780404c0b418044031031300e5000b015850300622280b40200c44001d1305041823480312842500182040001380140030091003d80440212441d0802624259212043e141c12220f0052822240d5415201c07000c240100100d1754444181c609596940d0b49a1603da901074101e69000d41d00d80c0e54801003c4541c0c0014806c61082c2e0f00c05855950850303232511038480 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 304828758 1250 304827508 304827511
    0x20d030c021609060504150312050c120f0706050601020106140f060708120f06030c01080609041106030a0e0129090a152c1501120e250605040e0a05 65
    0xd0440c420803040b6164100b8000e42c1d00b020b8452400041005880c0104000030341d41e00003085900c00d600c0010403c00640303207091303590042d0242e0402c682c440304822240c90405200c0b0305001c4012000180100c21000e00b080201960380c4507e50411184e161000120f080301c1150117081c6aa12281c4520780486c03401c605141c2812100600441c071b000001e54500150380c0014400b0700d181c44240c000d00c03c060034104c0c0320301c2d03100005030000c1c491102c460380000c12600c400341c004c50086801001280502415803069191040e000c1c006a6036424a2410711004081c002c001d12602d518145181002d1403072201e41850800640c00b1000c20303000b400040090314203020744020101c503560010070000e41255102c40000304440750441e8040c60081d00380d104c04131001c3d92103034500c040140403c40c1d400716806440800c10002c1c43d010002c9408081080000d0003006812580351041c1c0440020001e8082c2c40e003d62240240d1021f000c040c1d6542042c2c41601981c0144038210101e4000203030403080c00d500c0203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 304830008 1250 304828758 304828781
    0x70b030a09111e01020d2105070c02030a0b18060405030d02031f0f061205101421060114060301240c0b040b070e0d0b0a0c091a0903060a0c020d03 64
    0x407040880300b5400070310955464210316900d2942c60085503070341e603010704c00d0880c5a03945080220b0303c40c000300426202d002e0918044081240d0f14000300358514400c280c0e0551691b0f024085505c891180c1c01c1c200c00c00e20040300e0415a0280c8402101054000400c42034002c51b40040218141140040c51501a401c01021352030011100029103c2038440f1424407801040c100c0c11400d0f0280c100074008017030b07881c640b140360f80c068109814803801e050001d41c9601180d0704101d2003140f90751410001010048a9440141c0154087d16032088090010030098120381403019560309001010043c005a80401d106950842692800340956a0801d1000c0d6141041600c2c02410500007581d4400551303100fa1030585005480c1030400840c44d4001da01401c203a6000c64072000d0b2292181d035140c010504c01001e61008980780c0303102039195800384d080c40d805024210003440c000701a02e8407064003038200c030600611a200380d50100c0d442d240c2a1290f01e003012402e5020306a090311452058002d401c061082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 304831258 1250 304830008 304830023
    0x60f081203180a060f0605010504060c33020904061a0a030e0a02041a0306010503010e0a0305091809030a0e06090109050d240f0e0303010806040209041505040b0711070b030a09 77
    0x7002c1608000c0c000490824416140080c8502e0484001d000f220604d0b0805814404104801d108454021140000103a404407064202c0019000a102206025214696480240140d000700403229402030842e00c242600d0812070340d5910301d003803140c1c0c01d025007480d41e03018410070030805c100384030b0340100c4108482c0e0700840300b0006031503000c00c0c12141e2140600114450301e10840c11645414003d107801800c01320300910281644010305c9894010b02d5500505011000505001d030f501c0b00d8000c03036116840030080301d503c1c0c601842440d4072540100c061600092506200c41c007607151040588a0342c2c501a90b0303d01c0340c1c504040030f01248801c40e210a0310014131624166041684800450301010308002011030000c15031000c0d0000c0c2d0740c02e0ba01c404103d401c24401030292000014032954000d40480d8880c03081d85507070800782681d04a54513107040c0b1a0820042005100a8030180c900903081390b510700d5aa03a039034001c940e80300c007a00e004402400e0380c2000840d052404a40002100c035004088 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 304832508 1250 304831258 304831291
    0x15090901060503030a050d05090f102a02060105011209110d0f060504051b010c08030a02130305060f01061d09010302100e030a0b0609010e0108070303050d02190909060f081203 77
    0xa0b1441e008a44511700250f400142418850b03007a020700f40d00310070503400030110032070310003013142e00c0322102c40c5403c0f445070341c4020202c0c1581d101c0c0c207401250f40025040e40440900400000d407107042c2402214045095051228013400c640d20441000b5030f006840941c01541c07020400024100b031990a40b5070741d0f0314006440c085000d910440340210b00c1100204520f903001081480061034035030156041c05903159512021070301d20011254052000d40005a036030134440d588140440f15034001400c20712074a020040b2045880713030760505883c038907100d4083c203070840242040300c9044d01001e25042071284004000600303290046031301108072414606020100c280100307103003802d8a4803d4403400800c00c00d0105500b00881154058104031240e64051360422000540e6040340c7c0c8002010802c0020340d042d80034049605840c00300760b100704040c2d00304407681c5009051125500912400a00d4450000740f0030260713260a008030740c00c41018161550081420801941000f441c5680031201d01030f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 304833758 1250 304832508 304832519
    0x1030c090302131505010e030703140a0506010602010b0109050a0b1801030209060c010504120c030c03110109080d150906120f2d050d17040b190507030608151509090106 74
    0x19041032038843d110000901119106085021041582c4a14103020301220007180c242c40125401007540d421900c03001c40e00540703599181c50403801c494050030318002c50340081402603064224103100389090340e40c4458030340c540303040004032151031290740c943d03401c1040703034141807100304c0c0c908005200141030050a100d103d1010032020341c801d0031421aa03955981c01c01c42040401c0c005800307c2c5100e0300c0e0082d480d0b076032a500900910b1603d8006410f00c0000743e81c403807081d8003d410880e0070325840260641c95000601d844006040e06010304100700c8a40240480c107c40240315890454a027482d0804a00300b040c1c8035090703400c42c004415100c043d801502000b0201003411030000f40307240071280758561005800c00c141402a084c020004204441d108500030000707a4080c00d070004d0f00403025800d40e0315802d13015603141c525030102891450a00c410890080c1e01030b4020021104418280c3d280c4126480c00001c0d5213504032419035140c19000c4c1e0f000d01303906241c11041c2d841030741c4000002d803854552 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 304835008 1250 304833758 304833769
    0x10e07110708030d0b0102011104030b01170f03040e06031005150d1406040b01030c080a02010207151209050313060305090d11070308030c180102010902031c020109021302030708060102160501030c090302 89
    0x208060b51348940c07185c596040559091251108a403004000d040c102411642e0700e6402031018410109515056a03141c0d04a40c03003440070701c2e41c0c1c030f290f80c08a966903940e59070921008001155420312a000300820114120980d00901d4030403400c686100b168440c851040001d0302c407040d0b030289c540c07070b0b0221004020300c4420001c0601075070040c00296150340c55403500580420103500040d9040d0001c4e4086070050340c000620700c055996520241c0c20410000e403040301ca070425481c0c1485128145180309042c02800720003040100c4010b42003800c0151980c1095069450070385030880242c0c0804880180240306000342c21007040e590302554107503680ca444285040d0816070751803c00c00c900052004046030072000c0c102188000b03000900c1050350580000b07803185000044007804000a20207030100501c04c8d40700c0012503600604441d070480c0031401c5440250001c5078613001049041c00070a07429800010300c0345d440b01000d1302d500c40032401c10004501420160404030244154a00c003c4016a83c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 304836258 1250 304835008 304835017
    0x7380309210705100f0e07030b010b0306130f060602060c07110d0206120702030418051303120b1206040519080304032307030f12060f03061503081b070b03010e0711070803 75
    0x60300030101d02400400d001600321102c0311a0303030501f03a00958080000030f00c14035505045a00040340c15840c0d03907079030022583d080414008130350f40c5450503150706180c00941d40604141c800b5942121080c0e92000070b913020b5807180343e0024040e001c508a501c03d480c58418000040e6610140100e41001c1c02c01c3d180c017585174800e850002c05a0400305d42403000554240c5081303039401801c7c4060085080954030340c1c0c206003001c0009000c01c1144c80c000210b00d280e0f5000b0852601d000760a10720044600024203031146000e0f6422521401519040c180c10b500e0000012100784d000307440b251540c0c58541e002d0b00e035140c10741d005240d03420009100b2090b00d40000007070448c03c2c1c042c0d29000299400f0f1100102801c0304030102c1d0700420b180c09003e100c004a176091942c256030340942d0020f0000c1d41a03080d42c5a441c0203910040580d4030001e1440e04900034086004204250101201c0e0003070380300d603a600094042401000b0003070f10b0341e000080c00c0505c101114000c0144500075901c1098032070000a045600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 304837508 1250 304836258 304836283
    0x607080d020d0e1f140604050a09050609010906050f04020f060c0a0b0403171e01171f0e060714030609070e212109010806010207380309210705 63
    0x8078200082c3d0540503020240030300341d210310702000b01160480900e100c817100902184d0040384c2d03a000240020402e80d00140c45135810500700c420318644220464041c10314504104d60701c5080c0f5000c12801011180380e6805507900900b100845001481402034540003d140b151080c402c00d400301c404128600d0741c050259000380da44c0789032401040d0b82d03106401c00c050000b11805680f406100100030380c011010303040d107081c5aa0074a041e210410600d05c1c082035142c0031040c1d001e1002c0d690480001552001c1c840e61540c0e81035540c5a0b4030040c050303039070203080c4500c1c072a4640f042000440b10710707007a54100d80c801c0c0c890402142c10540071011407800c0c03201c1d40680c8a0004284000417840104200440c001500150301c3c2c41d14091154510205010300c80715141171022800225005a009000005c090448140009006240001512030304410a40c00c0c205440c41c1c412415001d90002044900c03800030030f00113207010b02c03038190078822001030b545a030070060340103001a60010718103200c643c0d1210b8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 304838758 1250 304837508 304837513
    0x2003090102030a0b0607020f130f050a051006050c031204020d0b040b0919030203190302041707050f01030204050919020405030a05060406150e0c09130908031b090607080d020d0e 78
    0x902440303e80c0c11240f8088200c0e1103003405000d500d005950300100101c42540907185031545622001c01d000c06400824840345025041030200235031101113a00940c410b400e2841d00880c250b9551109a403680700704140000540c0003008000c14594008603c160007030b1001d48010004003032600d0300c000740b14003903408a8520b5075003018054034120403c0780c1482c540c01e078480c2c801251115034010707540348103054180c1e4100841011842c02c240c0a64141c2d00100b29601c040306204034511441902d455083c0a0540710381201040d54005500c68425203042e00e40183c001041510380b04280d40f510b4412684441503140c0030072010034a80c80900186095900ca0f100401d001e04081c50305c20b05488800740759245015000310104403114260344a1600030740c032205542e0341e4408040106028101070320354050290b041c14440f0040000990003103105624200141c02038500240b041041e0f841010b0b45950300160903c01c0d00b0100e07c000c2c0c014440c24850034001842d0010b45008841600c1c081415403d458 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 304840008 1250 304838758 304838761
    0xe0901060201020a03062c0c0c0609030301032009180a200916081609030f03080106020c1014160606030503031009021207030b010c050114161b0303200309010203 71
    0x5a018000c61016155088400d003030b2041e24034442d04c210203440c0c030305401f90548001060f44001c1c541c040b540f121810b141500c40e0340c0ba0100405640e03600a10080700c034411890001c01252154801c2601d0701940140004050744808401d03050f0030810402c2000f0500542540c18005135001c486180c00015100b403100d5081d03d55000c1100e90400100b0303450102e8450002101010780c400101c0c0c0d03001000c040b4641c2c1d00f17200b040d02152b0582190f000200608402d002042c145a0011031050480381c4c07580c200d4882050711001e1140d05112003030020003055210321801c446040e0700000d40a810301c2a01a01c0030705c03a050300c03010b0603119145d1003030b01c1c29040041880013101c2a10780d000060b1500282c01d40c50410382d451039a0304114000d019030101950390b030844032181e01c2100c80709070498101d4020711503844003000c203251001c429128641844510482aa200360140d114500c038a60403d201e03001d54095030318140c01610721402d000c0c010140c01c1c1c1c20500034060340030155020707245050005849 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 304841258 1250 304840008 304840027
    0x616080903220f06030204050d320105240f04051503030d02090a080a0b0a052203030e0609150f0a02040b0a121109060a0e0102010b0301141603050106050d0207030e090106020102 78
    0xc00c40c0f5030805020140104010300c45901c41032810221182e01510003443c421401901d9007555001e13040d507000f40c0608601242041405400c403d0141e03816009036502001c1c01403020f0390307460340c10318030035000700c040c0100000d00d2426038800380d0300030010740d00f05c540c1852284c00a81503510540d076079181c0a60126020500c1d08001c203ca8014203240c4000702482803103500da41100340700060225003581e0301c1c0c02c0024a03454102c6400e280c191407120743d8480741d007601d20b0050003420400464000920030344000034010140000c842c0025180e405810a140d1545014403103024001858400030b56001c1000003a44900d100080521222a43e40c0801440c5203032203c0007520f241aa0020807090f0500284e80b490381c1d240211a0703e4422410409082400000140e001d024005c036495031551901030341750783d8902042003842c8107160303565500510051200c0e0641c2218001c1c004d03440040d40c18060100781200640c014049070b4060f08200c0045d00410000a540c000c090b01300b00010303500030035280354 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 304842508 1250 304841258 304841279
    0xc060c360602010b0102030d020a0315032a05130203180a050f1603020a050f01020106091802040b0402070f0b070c060f0b010e0a2d0e040809030d02061608090322 71
    0x41c0000380700030300c03804540f400000e65038001e03019420001a40000d00c8100c4500941c41100604c074200072541c841552803c01001490b800b06603c03407482c112034140c203c3c0d19840d0352a079082e140014801000c203034070070302410f0003504028001c0c1c90840405100600c00b0f4010400080d03540d00c01c00040c90a85004940c041c1060031155070401c2c515010035043c4016918102c42e1800d40b24203070388040c090078501004038003500183d4042c08045181071072041e42d2020240c020380d41c0c64000e450070310039001c000d01031004a218003a005080503803240008400504503031042908a201440d0413200810291a00c2003282e500d4450000c800c0c0c1d0f1180c211b04903580188c00005410411140c4c03070400c0d481d0802400e9040c66000301c0b840101d0b4440b04814007a00e143d4000000351011051510580c135140c0307440740d040d40c00b400754284244a890003510354203100046c86440740c401d02c800b594030340045010541e840200945041c126000a01503100c014510100720003810140210349045603140540191 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 304843758 1250 304842508 304842617
    0x232508030708070212010b0a060507060f1505010207140f0603040f080a090906050f130209010507050a05160b0c150408070b0a050105190f0b031b0f07030801150c060c 73
    0x25004d0f410311f004002a503031054401000c9880509086130744034104d103805801015007031000c140c00c1d85045c030340d03107000050b560008042d50001c0c1c08860b8585d07100c2c8040703041c000382c0c3c0b4489540009039107044810790070444003542e0001c3c480c01d11203122110076921a00300c0e41051980c08002080c000040100d02c4490042100400081c0c9010510704540004241c40340081c5226212154001030304500507489035007203500194010341924000103003483c201c1c0d15850300c25004009614051000304248011004481c00f54844c4402050840312040f1907524101c4010700c240c400e80c03814001640458a2550b140384152104140095250304000420810058543d4980d25a001c48642402445c04145034902034a030741c0c00c51182c807641c4a41000541880e1503480c80704555001c945042c00c112840080c01c0d5030707031081d19404002d81c1c98a049801d01e00515180f040014042e0b80301c90045160303648400003112031490302c80900d8101c3d508100c07010408003454000246408021328644140c0803500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 304845008 1250 304843758 304843789
    0x7080f061f0305060111070807030b09010b10180321030615200f0a0b090105012c0a0905160e061f050c0102070b010f032325080307080702 61
    0x50544007040100210241103400c010028141d4510200345141e0040c6812503000700d0781c0f4112002c01751030f00300c3c007a25159136100480350141c1d100c001c03480ea200180580340d8440b401800010005c84841d0703088880031041c0d610601c0c0030900f020040045801c911a81340f135a141d81200900307118840c45d000f000ca400b503912105108498954680b080380d40514010301c5140c04e07a11104204540c543c020342072100c000140381c8184211003100c410041d0520702c0d5031140d0b050500070022a030780c40e040e002140000c1034000105a049111111041c41042070700d0340c02c10b9040707900041107107103039460360300d4891441e08082d01c030084501e0801c51030030090b40003544100c0503501320494a150b00e99260b444225090b800307007441004200620a40070035415104031503001984420a543d50301011200c0300c405010564401205401d0f82c400c5030040c5489620079510f0f00c004107042410048010f241e442046180c1c103641c0d007004030014400ba01000501901c0e8018251207581d03410a02c1041b004d5407c140a2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 304846258 1250 304845008 304845019
    0x70c0506090d05040b0901170a0b0a08120301060813022e030b0a050d02031203070915020607022d01020c010b0126040f020d02040e0a061a0306010b0a02120307080f06 73
    0x1c0c0c201c2c01d50107801e07a4103d480e601c944645a800c1e21005a980c046900c141c0d4055042c0074040108000030384c0c00c0580c111000b50b441d0758910761140b45131034031090760b9581034903c02d00030401003001502c1200500c0c1d01c45144004042494010350004e62820100740400e64034950b031700c4040c69021017007801e00000c0300542c202041512107500101741c2200580c802c1512030140c2c2d0b082d07041035407401e120715181c49401d000120799034685500c0182042c0c03840d00841e48000c3c10001301485076800043d040d401401c090300180261300981c62504a0300400300280300c2c00d515280c49107000548240050030003080c4d8040003141c0c0c0d14103a800148210110310100241e40c0340d01102c00b241e440c80c102101e4115803c074200781c40c0c0e031020380003040744044418002900a0300d0000c602411a030042030104605210324001d00051000c00c3c80d0341842c115581341603515030040303001049010b4070800140f02501e50b0340181c40448060b01c071841c07501e800c02c95030740d004114030400f0859500345c2c1d40780c4298004822642e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 304847508 1250 304846258 304846273
    0x6020c04180212150408040603181509080d092a03020a03120c0b0103060b1801051e030a1208070908010903090923070e040e010c05120c040509070c050609 68
    0x2254003a240d03500c1000380c0141c1c944004007030f02c100140140c680440099502801e00c2c10305140180305580540b0564001a01c0c0c000071f10110070301850b406160b1904088044115002c101040000b0104440c0455520b4001c02400060b65114082c10580d5802104180f00513209960a252008a1001d00741581042c0c403e0510060362141d514609598020f916071640040f682010742e070b14000488040d09103946a80000200200ca400050b807481d019904916020105441050010001c3c040c0720b60210b170f600e40f03141a42401070707450580403a000701100d51651081d22040003d8a411600700b00064000040241c20741e04a6101d80080c01c000c0000c114941503520028400d803800e0003501040398454040c2200e480001980c40350030b07000c0612003401803d003868007500780300742c40c042a0700403030402201c404106018071401d210381d004d0391a03a80c40c044ca2000d503242c145800600103128044c081c80046550740ba170148592203602c8648070f44050a40c0c60400d189008401071007126a80e01404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 304848758 1250 304847508 304847531
    0xe070302010f18051c020102010b15190e040905010b09130302030f0a020a020a150e03070e130f05121b0c0a0b0903010605280b03090a1b03081306020c04 67
    0x40426021082d0303440c202e2849079001e50000c161407001d80c01103500800180c0b48070584640c082410214600c00d0f0000c0010040c00401c1c4204500f591140c0003002030305010040070500c1c4c07900c00e0f41410032146041c1c40000042c0001808030303903400c2021f0b115a90b42d41e021310100d081044c3d603290040c80d504d05803041c180040e640290b0b80c1c840c0c80c410380c18070f10022030056510350003046404002a401007110504ea621124540030426800b028940080d41050907050207060129901d402c0e612891000300b420f540d03001c4042d00f4001040070448090320015008000f0442c180001401d0054100a450b600e00090018059440c0d880050410316000610f0320031142da11045070008880c002d030b4010741c0f030320320420009005101550006070032410500d203401c01001c09400400b1003952405601d90450b03141d1403080325a000c100d075003420542c030055594002c20706402085e1801c0c007550015400942c0c0307a9892502e42e03004580e031a0340303008400c0003d101c129018440c100d042541510201700c02d4400c2e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 304850008 1250 304848758 304848767
    0x309010e0f1908040e0421030204051509240703121b0c061b0c02040c050c0a0f0203100c020303160f05040608180303070c0302100504020904290709030201030e07030201 74
    0x1010b00c012a41215500310801103100c00b500d005080f0f200c114250340ca13280c01c03e10500c1c428030b0f0030801c03e1280d0f145421541c0c2c6c001d02c01e660a42c1d1014048140c1d003c0d8000713601c032032580900c0c002588034a034442c900f008811045000c051588004071810307200d40040c90043c044600a5003008885411300034034804031003102e031446041014600c0c0080e51400c5a040590050044110072107850280100c208001600903180740810b078401d44e01041b01003400c0004a0f02c5015281e84000707207400504054011031502c059600000d4002001d85c0c4500d0403200705041140d42001c84000980c1001c4104071103d204d40060405000050500104984540c41e009009200301c1c0281e83c00d200c91000403411508000417042099022003080300e41c1d90030060310140c542019034400700c005201e185242403062a85000c2d01703004a40c090000501c6881d0340e65a80140c910314040d80741c441180b58040030708409060707031090043d6100d4513a000414110300004064507048102d81880b035014402c104010b0341e22 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 304851258 1250 304850008 304850023
    0xc08010e0c07030c020303131404090507180b04060608040b0a150603020c030c0f0a02210a022101060f080f03030f041214070309150c11010809030403170309010e0f 72
    0xd0118250340d0b4002443d0907981401034039406034040c4000708010820320342c4030154030180c0d84103621203121481c0356410003041e00e0602c0c1005111b40c201c2c0074100320003a03c640004441e810501070118000001401080c200d03102c41d481400041c403018140418045c901c80c1c1690890b04545040c044034103011500781c4254030342c0c4120001c250340000c44113943d030400d2050322049100e0030240c400b00c5c59104d010640d114180601a4803071038040045209000b44406481c40752181c88018060303880039074007004600244d49920031261550100c000041d86801e20030b03240078003110903600407241c0c01d0006042c41c10403030321001d9a075039000b0020302135940ca41030003140d406a0f20025000116034000000c0300c0d403980030140b0001d180004100c0d082051b801241840c16174961404880041c1c6c0190001c0b1241107105401421010030442d03500e245512034a00b03103900440c004100e07450141d4070b07902c0208035480d0f4810040212804400d00030075800a004050f8249804030007480c0b101c240000080d2150740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 304852508 1250 304851258 304851271
    0x11701050f0f0a03060608010b0a06170c041d071b02060d1a0303030108010c0806011d0d0819021e010203011d0709030f050604020a0b1c021308120d0c08010e 69
    0x66459441d1071a590300d0300c0c1182c0514000c2c0000d004030365640b4000c00580406d0161180315401d203180d81143d81001d07110302c011103401e603854000c0c3c203e0208104200040182100da42e04404201c00706020301030504e0760030346140310a01c0007080d00c0d020100910b00d00100d0300c200c1c0e007105a8914100542d54080554903030702c3c1c200c040011000d8502401034404d6258085e06500341c0030100000601c824198400c1081c95555141e0a52a9071504011600f42100008400d4004401150300c4040d0038841183c0440e00c1c0301d503c0c010314041d0300e072404c4c0611291040300540144c2c0000145500c0102e551100f99464008800070350455050040c4030030044000781c4d01486580f407000c00101e0003403081326582c0080da000000da402e882488c1c01e096440340401c0b2020703801504011000034010104508560f0501742168103031201d50168001e80000e580442480d000304c009030540800c80f0071042c000b014001c1180c654403903607a40000c2c03215080d904000700341020301041c0d00040042e54162a5520344c801c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 304853758 1250 304852508 304852519
    0x30207051e120c120304030b0609040b071b0615050a0b0406020303072601060314060a15030f06080303010e160302070f02010e010c061103010f140d12020a0b070206070e01170105 78
    0xc0701d0040b0628001802410036440240910b100c402201d0100040c42500c7c01101d4101840c0d03a03820900900400a603001048941104005030049102e01034080e80ca554403030f0403021030150350321440107071788051a000502c20100c0c03200f00b00500c2c1c40c038800d0006114071001107081c03625101c0084e459000040c40c1e20300340304000080c0800c3c40020b8410464810083c02c0703556565031152030003001070180041c81180942c2c0720010a80702d2401200b00e004035090403070440d800b40e250794000c030050050641000d01d0240c0340c04000c0389095081c4082c5010388a100b05292451800748401120701640b051404c042c18030400085003c81c240034140148140c083c00e1a02c06060b1003001215108454040900701d10f1a0070300c0c50010780e00c06401127048424170400c200c00580c580000004402d000407000380e01502074031140340040c0020409001006050058884030700c81615120300d905012130b51080140c1040041020710760b0003400c55501d003070083c41d14000d00500e0061030000088180501031240 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 304855008 1250 304853758 304853779
    0x60c070305070c0b07060e0c0307031403070b0405010b0102251a0d020d0603052104091a18090d050304030f0e031908032208030a05061306060804030207051e 69
    0x140180c048a10b040c1d80034441c2035680303a0700c60f030a58464000d4141140c0c9070341403254840d01c0c800c001031600d00f0610000d0280c2206480c40d0360341e1814070b01490400c1340038042407000601040581c031404c1e03c20ba002d240007089992a1030002801c10000c00c21101090078071101030b810001a4000742d405403280030325242c00c1d01e041d02c092007046000b0b6103160074460f80001401c0d661201c9a4220000302ea1055044802c01240390b46003003a902e403c1c8000c0c100d240c40030302040001030060b8100c0346640d106140d0520b0f5050005021410a5410036100300d42c803e001d5050190b03036030040104070f081400b0740c5410303170031820955002030403402e07000907a104000000038240b030142c0d828490503591421403092600b41f92558905130589130801c03100c506409224030758582c01c08100e4000b035034145900c48009861a5181c201c400000c2074041c00d501d4010b90740d800c00004c81f0304980301c1c00c00074003a1511981101e103000e280003894040140c00c01e5018014070752040241030600140c9005058040380c803c42c0b44c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 304856115 1107 304855008 304855013
    0x1e01020901020a020d020a0e04030c0c08030901050a0f0e031606120c02030f030702070509130b13031d0d05070605130f0308070b060409120206160e03060c07 69
    0x3580240f0281401442c110800308026407008011140c80350f01c522a040300014200d03422408641c60055072414420843d80c110014244280214540600c000000b0124092120502c050105d20010f44020034043c252000e100d04016040b40c030102000781c000620744109114250120b2040300384503409420f0360080d1000c4030001d4004604c0e0140300c4402c004c003944020a80421800380e81400304503503440c00c00c43ca0040f00000ba12503c03d4070b89040c00004540007030440c10b07600d50300405640010360458030140d603004d18203090b55184da00b01004980d10303070a910340043c014000c16102081081d0080c001e170215008103240001220b440d0581c80c07403120164040541040c0050160000203405520280e61090000d031012840d074042c1ea03201c800c000d80c078103001800b6810400401000240c1240c0b9100004800e10301150300d4007039080840c0e15206d018001100d480340010780c00c2d05 = true := by decide +kernel

theorem cover : BRFrame.Cov 304676258 304856115 := by
  have h0 := BRFrame.cov_init 304676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 304676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 304676258 ≤ n) (h2 : n < 304856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
