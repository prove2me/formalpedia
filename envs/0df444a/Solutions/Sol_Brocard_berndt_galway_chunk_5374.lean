-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5374
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:39:38.457656+00:00
-- url     : https://prove2.me/submissions/ddbc7a69-76e5-467c-a61b-7a36d17b70e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 966366906 ≤ n < 966546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 966368156 1250 966366906 966366911
    0xc121017071a04030218150907111006060905100e06072303041409180601061e050c0d080402030a0b0c13050102010e0d1b0c030804140114030a0203060121 68
    0x40d00c1081041090741e14580c2d080c219003800108056150550b44841d8140b007000001516550245100c41c003c1c04000c0003a004030082c0d04000d0f95a4100d005003042c42c000303004903460003030080301b9482900d01c1400b8180c002072240200304002e0410078445002c1013203a04000b4130318000c4001007034440d04400002e80b424a0540d1046920000401e10401036a080d0409580742600340846545140d241c0101540148082000210710030074000e00c58078844158002c1d5015541d403000700500c044000810b1181032040d103281d214640b402001100c0b00304c4c0100d40580b132150100e006c00d44102c0720042c4203a805010f090038000000e00602405c5100b5409030541c50748500c6407414503182d43c10107401c06415689003d80c2c0080034034001070215507003800351822519045400326040c000807160341c00100705082118020040048410140080c0e80300d0380003d0401c400d048004542041050070900303209a0b040002c0340607500c40d900119800b100604044041c82030188100d0001005043c070f441c4a5503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 966369406 1250 966368156 966368159
    0x1407020a08160813140909030301180f020a081008151605090d060911010c0f0611090d0303090b150a0303120605130506040b12190f0606030308070f05030c12101707 72
    0x301815240811850146c03051200c03850601d070140e580780b0060040401070030040300c4050f80c11758242c0022514101d461025500c58141c03071406000941c2c00d885004405c80003200c0810a44130008032000415003040702c40700b503911078122a1500300d00d0325802d40c08000c002c0141c04038944880021b0b1441511030728001a50100a0500c11110780c0150440307810840e40340e80f5200030964140381c0b58442c1d40c12000c000303a6804841640e0700584035228540342c0090036400c82109164240d0700401915020341c80129680d40e6440c0d40c1c4440f9045940d429034043e24000040c1301080c4a00c2c40548626500f070f0000030010303140c1e40003030780c101e803882c465280c49038850003084201e003898007454421100075942041005c00c05101540c603251b43e0051440032200b400e50302c5007030042c02030502d10203580200040010076140c1c02d00606120044a501009c141541c0728106240e1084007124400e00f0300aa0301414030140107424100032601a00b4081c0c1c0c962004000304031008031084210845816000600206 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 966370656 1250 966369406 966369419
    0xc17070b04050d09060314040212010e01050a1415010c0b090a080301030606090e1c0c03170a090c062a0f0501110307030b0a0503100c200c041407020a08160813 70
    0x110640d04441c003010b01f890300389072001c0c00c80b4944941080d8104e80140d010011508120300500d004110065950709003028800303a54482e80c0107400b10000c1c001c0f0030039149d50312500a0914404801918002400010840081032460382c4060300500f000d02600d200d180f258482c8052078000303801c155900b65960703a04200c5919140f2a03043d85090000c050491002500b80003040c103c4640c0c0100c0501281c0c40d100420944034400240303120300c260300a000f5505202c200d0364000c00c4e80f0b0764100d03510300e4240c802042550148000c00d01c4d401d40d601c40c010340004003c610090b0242ea58200703e480e8058200480002071007030007500d1b1010901c606a079181c1c42e2450b001001c1c1c0e0301d02d641641c0100010310007440281c40100300200511414680440c425045507800c130390252040e003400c10662440031044c1390800b800304800c2a00c84d41203078184480070b1161001c134280c08060b40c9003000340e44580c40c100000b840c000040c00b4050700c02404400d040c412611741400d030364401070888813100f05006040c03004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 966371906 1250 966370656 966370667
    0x218010902030a050610140c0705061b190b04020607140f010b0301110406081501020a080c03040608010506030c03060907021606020106030b09030304080414060d1b09150c17070b04050d 81
    0x718908407605030420410360005000040605440c4031300050024600c8c50317141c01002903400074000600300c0e5030b4820011402101c00d00d005680c00d1154007d00b00000c8041101c4d65490210030b401c444918460344441d030070042d256100d40c104542c43c3c0300e104603014042406200e8110b1540d865000401c0494500040508643d40d0407040b034082402480107100403a48201e4065004070b0703c0d280c69240c26080d40050f86040d8010b080101850000510101c0307504000c0090b204907142c079107034400a40d03203c004015980c00201c5444040500c14000190b06103031003884550811000e0040e0341d41410380c40c0b43c006050025070071480150f91948000c0080141c1703040001d03803044074100030314107500f829500c0984500ca03500c144000c0c0b47d100058501c07183c0d56001240c40b40c80d61124108085d942d2504080107600400710070b500840c80505001400f10810100d040140a41d03540b800c2030358a00b030f0f80340f005070b18409212040700c40d000d000da04000784d0124481c50140f03024100400c116003200100514 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 966373156 1250 966371906 966371911
    0x90606080912160303021305090c041809031b0312050a0903090503160302190b03070806240d24121202071208070317100614090f0d0218010902030a05 66
    0x19a04803c011004590341102030010105500d45005641c1d400c40c1c480e103501a1401da009039a00007108418014001e2480000344115802914403d8542c5a071031890320403240f42c8070014010900c0000b18591841c6c0500001109074401d040c16005002c3c0345801e01d007100d40440e11000c000d40d84861482c14141c10202c0ea00091500310010600d030410882c0d044204da80f01e1100a0048800300325842103032000b400510040c0680e04015030b12441d100384018075500c010b80d8020b0045100600e4940d00b40880b01e856001030404035041d601d0496010224001041e810700f08a0304a80914502d1400041c0b00340f0040041125801883c401078060070000250100e482038103083d51700421041010084a07000700c0c031003e4002c440b154480e445410140d600c0c46a10800c528902c000200700a07110380303410b000a06071129a42c40c0c402e40c0300321710306603011751080550460344840503da01e80d4161808520100f0401c0c0302600c4148001003080760007040ca4000e0b0000c1012039004010060860f8a80c0b082c82d5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 966374406 1250 966373156 966373183
    0x331080c0723090601021e0703020f0111070303182c0708040b0601120f1410170c06070303091203240308160c1d09070f0810090c0906060809 62
    0xc0718440c141c40018910042c1c0000c0c000c0d110000040c509030700034814002102c0300d910f172040b104802c106070292940a180002c0f40b103050348211075400795128845250504500d000248401821920300781e860041c06101404c80c1c1c0c66078440803032040b003c514016a0084000342e07102c000c490400c0545103d030300003805c92040010712020080070070012802d00340c10000c00e0804400072184040341c4000382450300400c020150501034003141c4030444c060319500c1284c80c1128103002648624041c4141420000d5202c100e42c4440101e21091801c00c0c02448510311904002a8448459640c040407030384c5100f00768007003680c84c45005450511070030048103011010701d0b144402411740e0342d40340032402821018000c2d80343da130140074200554628401c0140c940e0805d4203514003100c28440e1a0840d007150b1001c902c0c001e001c400a4150180303004403064981c07070300107000e041d00c1c280c500000421403068192142c540da1203000605481e94814800a846156201059407410b1030169250030f0320f001041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 966375656 1250 966374406 966374429
    0x40807080f030c1b0402090405010b0711060a020304060e120f07090606020a0b04080307030e120408010b0f0a12060213060305070323062218020319080331080c07 71
    0x40702c080c1c2c007154540083e0103c164004501480a000c05c000703000707607024280c02502d00b9001150303200008001c1e11201d441141084004c0510000f4410b0324000c0300840405a84240014401d69024205c00148504040e02c0030300e400d821100094070382101c8a1480b045038100300000d0158284a0146a01a00031390000b084001030316a50850032500050000c1d02072140840400c80043c070076000380c2c40c206113800c2240c440d80d1032401501c0c0142d22500c50750800351b28080078500f0a08201c0b104070040c2200500c00951185441a02c84e00e50a050004552a5500b0070080b90341c207400c0c04100c2e029102d0f5581c0001c2c00d180008014046600031000b000034401c01c02507002c60041500d407025840003090f00d15962100704d14a5a12048001080000b451410254070160503d400c2041000c0b4a008504440709188020940400b2403504907003d4601e680c20800101e50140d2504c42e500c0202048030454141c2141c603070b040d454014929003c03184203c2c00a01e005c440f003010401c42000e060382c0c1900c0e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 966376906 1250 966375656 966375667
    0xc07060503070206310b01181404030e060f04091401120c0515070b0c03040303060f06080403201605030f0708100c210906061d07180803040807080f03 66
    0xb0303580380001082c5480482142020f817040314526100e0082071070012941a52416003840c140900000034000d001c3c45a80b6242401c010384e4050141c40d0b400c070394a10680c103881c0c491351030841d850150f000c1890b402030340800c09070000c14601c0b00100010b03c440b502c00609060844035016814906a020002c1205a80c10300c40105c0c400000c01d50446404840d1601200702201c000480740c0501c600c050600c0d4010401c12003400100d200440c4103d100f075a0400c040c075150030f8000c15102c018040c0b131303000941001c00100000c2c003501180c002d120364005500101c005044d112890005032450b440007900020801b040302d402c08100560601031000c0140540b07900342070308955a51554110f41d0300c42030700c55150b58101802003e030541c604d2406a1011413a44c680140c01e0003410340c0090413a8028505500022100c10f4800d9803844c1510940440c3c075103803910070040b1180d0802403407100b40c030050300d600010b00f0b08040006100800307800015040305850450014101058030b0780b210340a030000c104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 966378156 1250 966376906 966376921
    0x10b0f041407030504110402040b031f2405041203020a02130c0e0105070204110f071104050403140d0e2e0902010519020c3703021318060c050c07060503 67
    0x41e403100d4546000611381d07495040010b48a00301070307820b540052000502160b182c407100000d5100d080200c00c89603444500106951807070441e07108540d10768001032140300b02c08000500c1104100c1d0149041d5050540307d805018219901c18011000350384042600c0c0114282458000c00e18500130008106d00d00d003551000d03284605c94500039040050000d00d46046545680c00300881c1054030210b10346403400e00103810f00303582c007020003540e20303281115003500c0c5440d00d070140364481c5915545100c040245000e08040c80e40080392540341c125100d0111020280080000c40101c1204a0716420714028121818812040d01407208040c1c0b0b0601080c840943d800008889001d0400c044121602c2051281241420421b40603194050307a0500b16855812084040902c11031290020b0010302d400380720400840c50840c400290071989030020f44003a621583d00c4140000d241201506945c056a614402100c81c01c141c00000700340086400c4105040400845000e48101d0401a146080540 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 966379406 1250 966378156 966378191
    0x6030e0d090b04260f070e01230d470c0f0309070f142106040303022b051803031b16020d051f09030c080a0c0c08010b0f04 54
    0x80203800710121300c0c40720042030411191410b2055031030036a51842207100d1420340380e400c24031500312083c0c0000008943c600c40300d00a417100104000300103488021031028412a00050102516130021005152081206d0302c03c5200302a5201c5084a42c0c1021142004003400384100200365000c16200070801c05405020807210040300d5040306503140d41c1d404024074a40079a58001c1610f0540f4080c0014074461102d0741c0b07044249040f42d150603045502030800344841d1503000d56441c503501500c0441c0c0841c2c001d07801000d08066030301c41004d0701e5003c0c03500301061006462880706010780d01d50800c81b1b258000d820141e1408070910145107581401c10b25505241c516400c000c400d1040007034101c880c055424a03401171564080c100ca0110401410070381d8940c60381000b8001d1311030300f03120010000801c601c221941e075030303145d21014440310451711100700903040340105509101201c00d0b5000850203003401c104c024021400003040c03280f00705090060a4000365211130190b8105a203107140e562216 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 966380656 1250 966379406 966379409
    0xf060307080f0a111f03020408100b0306071809110301090c080105030307150212011d1b1c14190f090c03060e07050603090c120c1809010608030406030e0d090b04 71
    0x2070024a0213400000900503400182103800ca409501e012540f5181c254002c1e104448504003507a24044801100d0740a40d9901a54585d058201c000000c00050182411443e003d40c5800403d9500b6211001303001240e60310359089003034500102c010000010b0074007c0840482507490701d00402e52400010903524052100b009050100303040c0d80003000c60150303041d110200c1d0040442801d41d6922520b13988104407012942c0700300403101002039200c000c00f030045038520082018003407400f4540d002e10b40701441032041c0c9100b0241c551803200b10700034400c2481400b807080da10140c007800942d8840d440031510f1a0b45208075050804112300301160f07203040d400e011260000c0002c03400c003050b08081350500035283c00040d0702c84408014000e806000184402c41154140d512411011484c035210303544444d10b9140640c0000d03901864000706a03100d000c90b4004107080004508140c82d040100d040d5002030b00b141c00020341d40c1042c0d0034100c2d01089004180da1090400b6910a4103001d07001101c1d2045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 966381906 1250 966380656 966380663
    0x2104030c05010f44010602070611010b0d08090321030c2d0301051003090f02120a0807060f0f050402010207060503090309220e0d0206071803020301050f060307080f0a 73
    0x3c030341d4520a00340c05100c6081603011a0010200c02c120342c44019503003800314411810300310408401c4c4440c040d402104260580e5005e80052561505c2c01408072462514040184002d54840808460940f1604018080c0340e21503401c082c1c42d42c034400c050601d0100e11910040f4a02442803d00e0008dd090300200c2c1e130000110110720740c0d104811031500301003142d030a4228002009190990b0603902480010b107040e1401150221040007540508900352128080040d0a00040b03024000061400070113061151850720b003a02c8404211b0b40f81c042442d0803095065034195201e00c041a0a48070038807032010b401307180d0a010413040c00d0680000b035035552140110400d0100010204030b44034030800c00d41e00384000080803d0380880c0980351107405805203d0b4501c4686003099100400b504020464100440a65004146070381d221070089680e002c0078203004240103403844010026803002e00030305100d80316113040da52060900c03005041c5003041503840703140c01341c02280005c0080500481c00c0440c40d40c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 966383156 1250 966381906 966381917
    0xc050711010f030603050d0201060f090b130f0908180405011502030a0c03020c0415030b01050d170304031205130b091914030d02190221040b0a18082104030c0501 71
    0x701000c0030f40c014801900042c049209482007020f07401e03815000b0005950400c0d0400b14056917800810041e10108490550f104d0190245401443d0440d88035980e41080c6040108901006407602102640101e4880034200c14182c5000d1103800c05000b864010114225000e04800301c0e010001c0d20781c0181e103141400c1040030780c40b81061503c01c000907240014011300401030864a10401e21440702c6030300c4119010120300c000081d881c500001080810390b044022140030455100507901c003035000400850600000d41a120801c2400740f20304e034400c500f210300490003100d8a00741100c0e045c0005264181c560f00048481d440d0010700102c80d040da07980800b040c8904030032034410a08600401c0103040e0300e0707803000c18800c0b070400e56115031480710300c3c450b002e50341101c4101c0f07900742c0d240e0080d50080c40c042c007040004200740d0484a000780701540c040d00e00314901d0070b064441c010100401e50300008143e4070240a1b0000e40c0c820101043c044140f80b4603051400d031850740d4410b02c030384091003564140079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 966384406 1250 966383156 966383177
    0x80c041a0a082a011d120d0e1302090a2c0c0301054603050a050a152c010b040f05010612050f15150a0f1407050a0b070e040203090607030c05071101 65
    0x5c503421b80c24540300c110501520132585404800614000c190f071a6603116102c071401c044044840d40c42100d005210140c502e40c201810b1070040c2c00024003400d240308949400703003c00c0d100f094202104500406400c0082c5a681d4507080801130003101a41000703101015480b018241c01c0403144c202c04040009004d004410040e904003100c481a65130f2018100e802114100001c103c0c0104502540d00d104a007034070080c17001d81501c182100d070f440c1e54074000007030039071080303501442c0b8003401c59a038040e001d0000c201091004040b4068038403110204100d6034071580140961600103004400400300c0c400c0404c2646411400a1702c44c00c80680752814110140ca05900d0a4032403494261000c3c2c42401550f03a00d001002004207003107141d502c1c4c0f40001c6d0740c051b1409201c00e034a500311201550048000c260540007901d910810fa5005480c042c140031110543d0030f550b03120b6002030f610407603083e005001301c0c0c86c0c0030302d000e026518004800c008112080141c64000742e10600200c040d2402840c2c00140781c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 966385656 1250 966384406 966384409
    0x41a0418170703030518030a03021b0a11040b030a1a040f02061c05160c1401020c0703061e05011a0306030a021c02031204080c041a0a082a011d 63
    0x8526440d40a81401074072444000400403560061190030702c02d580800c041d40e01d1810298110303910700c082d01c03030716042000105482c6d4802c0e00034251a000d108041403e007001d8424051500c0b0400c0d80480f00c81c401d0150002c610300c0c0038070642c44090800d0700504170342150380d9030781d03144105002c481810b92a240004102030064075110801869030281c0b540703503600131b02c1808103003481000460001a43c100710000e1803c41c10904001440551900c0d81034010340d0698400001d400f40c040708068966007840f07210140c4108202540046019031000030380b00c03100fa55071000500321010301400aa0520004012000c101144040781d6000c4650290701c07070300c1e4580000d081c4080740e14060b51041146a20001e04695508120285e42c0308030122200e017807800d12840560701591082550740e4000700d01d48201c81c04c00e41c2042032132900b425a011604a003040018401c0e40094000c02515480000c070080c0181c1c8084014411783d2014402c141d0550507080000d00c00140a030360b0900d101c407824800e4045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 966386906 1250 966385656 966385691
    0x18041505100507050c03011107030507030314010b04170303250201061d22050d030b030708070905071107120f110a090509011a09280204060e040605041a04 68
    0x20300360080c003511104240c024020200e411007901503c5174043d0703400e2951189014070070144407040307039107081b801d06003140ca040c3c54035040300000350285503d0340540d00b03d40c03c0d20314116000e0700c5154142d07501e0300c0c10080705241a040340000119280d00800c18040c407445114502c400107814107000c00035520b0003a004070f01414180d40104070318040701804001d03090612440074854086000c81c8680c8404d416442100c40341c2c20000134001780c200c1980b40040e81d109800003080c5c00d078003908541c0388075a181111442c1c0f400e00d9000e45032240c0c4c2c0b84184009c0c1c1d944410042a10034584004152290070183c070140245001d5100508442104900c202005800c45d02510511001000810300b15a10400308018080848024215519140c44103805a86085039602281d07005423554481d50f50340d000380c3c4004801180c044030044018005218501d081d40010005001107589091284003500207010a40307446402081c411820032680d07034804004002840391080040b900401c0f91002c05c801c6540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 966388156 1250 966386906 966386909
    0xa0509030c0307061b050901080c03101206020c07060906170a0605031005060f010306080304170a0203031303020a05120d080a020c0102070503071502041503021818090d05180415 78
    0x20501011400105102040c5d01661300000c412021001c1c0c1c190304034044480d03100f0250b03000d021848d080040b81d0248440400355178803180e2a012080c0c00b81d01c03449507007982c0c040c030001150300e10340000f0201d01e00e03001400408020503607070922180e014103003000903200700180410b0700800000d500010f00c205803c1d4001d01e0042c4406400d5602c80018040144050300007100e565009501c0400d10039155407003840f03410304076101d8002030350038207061000752172090245209840a51040d4000b200250b81d050000302803501071042c00580e19895441885840700c41580301038400c0c1400c5070383e031030044d1011641c0482c2030464640311010385d0390440580c0c0240140f5005004940c030105100701000030020060904030302500c540701c0c000d6046a00d030410392046000d0891360351144080111454060f8000e066000c03582c8020090800c40744021071009043c8006c144900304c0c0100c284036a00006010459644220b89421480c1102c491007103084c028102c02e06a01450f559101081d110044c0a1002d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 966389406 1250 966388156 966388177
    0x40503060703051e161806050919050a0f09060803160209190f02090312040f0317040306180b36120d0501050a09423b0a050903 56
    0x1015085c20105040e1070f2410703400f844007080c0710b170040c00c0307034010441ca00c4003c40e8400d68072540344c03c0d0400c007071103180203805100761603807440c00b00041403030f41e520f494620103883c6100c1002c400901d010762010644900d40e101c25a0741e042040b00950007030891034144401a01641c0841070b50f29240c1d061076044000420103052249085200da9510b030090b0014072030414110101e81000b48a07582003031543c0b02c3c91003407807103030400440c00700001880c2e254940f01420040703001c0d0307062641d00e481d44000da441c5014107040c552005d0030198108182c5221498001b00401900c03400010703000001110094074402164555010884525549608100303040003816501c105503252010a0b011a010341005c1c041c50b482a908028081a2008184109904101d066920141500c1e2031942210141c00d080641d0410480b06c00801e8402405c183c1c50700024200440180c42e01d1100d10340d080300034001c0c1034074041e0307100c0034010541c40d42c2e0410000300c1c0c21440d03e010008594075075043c11840e41c4507800310340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 966390656 1250 966389406 966389461
    0x1419090f1b0c2102210c0d262502010f14060a0b090402070501020403060b033904020403050613140c2805100509040c0801150309021216031704050306070305 69
    0x100f491804e65005800c1010520341217a0702c2c1f12040c1400c5c0d80304080003035107810442c00f428680a05807200c8030b07419004a0240c803050407610060798107600a5250855050250791103540ca461404d13001d106020445186014051290401d000011701201d142d205541c01c4040210300d82e15140e90b140d04a41441e07920000031591185ea920345480580880c1d03909510a01030102002d4034440712110b192610141540e403400c1c4c0d2001101d006d00e0709070820064941140e17090001200040042100030302078007400f03050b030a07400050b10f409800b0300701c00c4031941e806400280740c3e44e080391a40c0c031690894030388901552542803125000070840d080c0383d5111580c001c00310038691000175001402031400941c16202401805402d49060381d42c00c2e828420310149603103090700c040300d09101ea0f0201e0012407008011840c0320740b0556401d460003180c1000c2d1018070b42c207004100100a40150a040c1c0c616090908038146440d05000940300d000c0184290f041c561500d00013a0309007c080c5000c05000e0505900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 966391906 1250 966390656 966390703
    0xc10020705040f090c150516080f0c03030f0901020c031602040b04110a0e04140609041703070e13050103030503010b1b0304061e08011419090f1b0c2102 67
    0x1038030050000c18505652107100e04002062510314408a1b030080300c42512000c0c68400c0100c111000d6603010304080d50740741c0702440210b4000742260010402d50301c2d101c0055481c1e080190900e54001400342400a0070f0384100042225041c01201762103160001d650360300d411403e1400072402410700c1244495000d85002280050181231300094030b011000c1d585d4030070b00c1e02195000c0c041241c5420003000340f0a440003002900d10716020708116031080c4110a40d468201400b60311100e160015526040820f001016550b039a05090010000010400c0014001e6514680f000340c0244418054200050800110194403220001e03016820800720422603070f035940c8d2204010154140d10303c2c0c1000c260000e5407040c000c58491102039041c3c84641208074203582c65901041031001c011604006003c480701c80020714402d0718030a4804031880080086804c0191829026080302c05100138401d00c419a5071000100c2c0300c28200405181210542c40500960107406070f281c918400ea0355210194074010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 966393156 1250 966391906 966391931
    0xc06110601180f18060509070e0910050a020702030106030c05031212010b07020d050d0203090a05040504050601060e01110610060f1b0303090804090c1e050403036b0c1002070504 78
    0x1c46c520640400782a100c20a4030340c4c3c81681984000d4507001c40592050258510114103035100c1c641214006800500d8441c0a9020a00f903400381d901c150341c1d4209005c001c21086c24207101c174500e11394448201c20710700701054200401c2c959040c0034070b80c10170502103211001c549860f40d0800c5507940160850359040c1c01d201000355240d11401050340210b9940100082904240c01824080d603071000c0980f00c107a0038018100c60f1540c582c004541005006096648180302c06d20a25000d4101d0f40c0b58544607070300700b020107000344c500e82125900300308101d2034162203440c6400040840c41d9062501180c480310904060500e0300658000510151500510815154202074040c0d0400f0503003103074003116080c0100c01c0d80c650041d4440a0007080024500001d04a1444104442828103401450b0501140d0700c00c0e02081c00c1c44041807103400750207001c242c003602c0d100441030056080c91a1444010b1110318806e900c0b4030f003141070180507541e040031402c1c07468000e1000b080640400380041000703068080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 966394406 1250 966393156 966393161
    0x170303150609220b302d01060e0702010507020d05130306020f07050f100e0118060203100b030a0c090909021807030906090c06110601180f1806 63
    0x1540d4035419201039006503034505240303081d246815802000140b02076055895509041d8940025060255840c007014260780d580f00341d030a541412080389521511203090510720701a681700c0441100340c0c00b000c44140761441c801030030320342524400084d040450503243e2007809405641c10400d00c64500b481081161581544507521520395a4200c0b520925034802c240e40c103118648200781051075049050010800e01d80080c1a5001070a15003850120142c50311400c0803c0e000704118290042c0c2000003095040d80500e440000750003000700a000e0390302c05441100118080b00a000c0d07030300440010145c04001c40010010004111507660360302e41890114002c1c0520340b04400400d500c0382011544000500c9080303402d039801313404108603000440c40b246501c00010401000c2584a8000300c0c0060020b016890001d44251200400c241c10418094090784403020708107450b07809200100450410212010b41d078403041d88000915114031f00500010707084464500c142542c169414004028407503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 966395656 1250 966394406 966394411
    0x61501020610030309090e0a0203012409150303030b0d060504080a0f0806030c1c050a0b040b0106020a240e0f0717120f0d06050d0c05030d022410170303 67
    0x903800d541582d91440c801400b84003580c080074001505211003403101054075808007000e0000d990855580d600ba683c00203095030305900d2440c2c0881800000401d25010300903003040500300f845030a00144e000f40c070b8549640546440b0150400d07440c0c4090640c10707220609400d00580d00000d05003d0b500d882d0811441c541c2c490f0042c1c50008036000c030b051006511039424540a001c2c018054058104101c0410a1030254602e03501c4088203d4425580000c07010464042003034403450421149151a0400280d1070300145c0c0404155004800d84000050180c0d0504e0312401810740d01c02440206641104014005c2c51070b0700403c1d00c2044d0034020b00d1400042c01d882280c0c8040000c1c0030320481081000c3c4c8400340c1021103408440203016001000102602900321038100102c00101541d40e540005c0c0600003a00341a1403060005c1424401402d080c07040e034143e01035500080082c501003050410000c119032210040a0001c480030528903c038034600e00000b00320710440702c802161400001031f100ea209 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 966396906 1250 966395656 966395659
    0x6030b0a14060103060317070302030c0d0201150e090604030c11030703050307020a08010b0105070f32060901050c0d0b0a080105090616020a033c18091406150c0615 72
    0x8200020110b41c440c0c002c1e5400d69500100944012607011f1300001e094111000032001d50009210921205908200404240c82c4c1c541c00840ca04c80380c088012500032058204400e84018031040080c14240000c241e60822f82c90300c0e100015440a0514011a060403001964103015820700003060041c000041c180b228001c4810341010343e9191420b03802c0b03902c101c464a000c50414030600000c6800d1141d04016a8003caa100c0c0c036200c04104611610342060280c900d01d00034645000141c8402001010341c41060700008100500b0802c1929101e8000c0c458168402501c81092400948032106c40c1002440002c0003800300c0d003440c0c010252102400c9589210424031043c020301054800680306812540680759008071804522660340a8540401250104070003021410051246100000b450142e507070354185886c1c0b205d03000c810447c4002c2d070100d403911341400e050601444242440c5a04048115104000501283c800084e0342c02042c0391112503009080411005111580007041d44280 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 966398156 1250 966396906 966396941
    0x25120e01030f0b0d03110c04051e1602061302010201020d0c0507050d0f08040605071e02030a0e0a0b0d020a021203190c050a020604060506210106080c0111100207020406030b0a 77
    0x5044442c000c07100c201c50110351003044c400c1c804002c01d01540c204541d080000d002d940100c4143c20114007560000e0310005480a1440c42142e00b242c3c03414400d0b500a1f11810202c2e003000140c40c0001d688103000b40c02d0039144003d014100c021a8008d6044808403044504203000000050380094043e8000e0758041d50280070307440310307084417510885030078481c02e4141c0c9030840e02ea1510f485080041c100140b5274002d008030714230700c000100c28061584007030b41125401956503022660000341081c0c0121000350107800301600c1801070321484815220520040800161950307401c0e58100c0c50090070003100003601c4000014024044041908000c0c000c070518001e021107600044215440d01c02c0e03039000300050304031401040002c0c103a9007000ba0010001080481031b503500ca00ea40007814482032507219035030741d1650b0400901c0814420b0200381e14090034205411814040d40948400c0045642c00d0740b243d002624500315952a48580080c582141c0054400d02d42000070000402c5240312f461038000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 966399406 1250 966398156 966398171
    0x1e070503010c0f0804030e1314060f030c0f240a02030903070509010e0f07030209060f130e0f0403050c1c020303190e0304050d06091b0f120825120e0103 67
    0xc2c040d400c9100f1842c5544d4a6000907921a2000c5503404c00c20300103184e1040380d0409034192101e150150150315461f121003690f031070410342c00b00320128441c2d80400d030082c1c0141841804503918409000001d9600b52071041600d404500260301105181e84801d101d00404a10000801d90001c080c00c09480c003581264081900d070010010700c10000d102e1844154003400000340703503150710807205070400c4183c1400350330b001c03502c400200c003a0403039031800140c88400301d0092094040441c4000050881d849008100d0900c4200b0030180c480040c80601844000140c003411200c003045549038020030042da01800b0030034010020745036070084c0c03082a10b441f0741c200031100f04d00e000c0c46807401c8000040000c0d40b40500d080140301154070418010f880050361080850b02140b00402c07041c002c08072034110714070113a00300225010624160382285864140400041000803100030407940f071000415101d0303100314074000d01c0260740502d80c0801003143c200000c0e6075a84a410a160b000302c000c1c02d880510528 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 966400656 1250 966399406 966399431
    0x806091609020315010f091a0d0b0d11011805060f074d0418030801080c0a0512030c070e1008030f0703030203040201050c01050c0909150a030308091e07050301 70
    0xb40000c0e07603001030034000d8400031034031136009280307a8403446020b080601f10716507500944403500c04540600c0b03031070308800168003154482c1840b500844400440702501c10441d00d40351501441620203d00c0d042c0140303841b41d0043d080f14003003900010040102950741da8070f0320410030613032904810400c031a81140d10000c00d030f0b80701100d100c5141404840007109984446112101100c07072103c0d50300103038223159800018580d01c0754013800207030807140e002650180c001803500401c1a80140d22400003600450b034100000d80d40c28252108481c002c68102d00c4030120200c1090031446107070342a00c070350f118040c80006c050b03140c00511446022001c0b692240569180d80703043c1c40b44a420810701c1040010495440000d0080e406580c100e0b00600d041400d1801200c0030030b08451701595240b00342980130403a0003a6150080071644d00c00c10181c4420b040305543c03800302d004011580001014400e041000604415040003d103e148041c04c945035807445a44600507141e00c21400303018025428031004141c81c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 966401906 1250 966400656 966400661
    0x610270c05301603060e0c090109060f0c0213180b1501170a020f130e15040902060306040c050f2803091e021306090c12050c040b130806091609 63
    0x20501580c0075003010f0340e0380004280010640c3d01c8050189a960080401c03880c0341d1070340302841420161280b940c0e03070300c1050001d090580654840010045102d8031506802c1d8001c013015602503060390300070712640e2004035041c003030b01e4001a5001820f04000c2c080c414000e03d01103c070b000f109000c42c8400340d84500307c01140c40a00b80c034903280c4484110000b141900e04140d00410318010202d40c560300380100084030b0001a0919805104171940d400c06220010401c00410b12000e001142d0402401c001640800c0540c000101300e10720a964031480000041c3c001c0c2e003140c07540c81d07505001590381c00b1195100c00c2101c0e45044200070000c01100d01c540e40074040c0c4140c000103500415411021150000c080e001800c006004a03000844c020980070024542e009880103000e804034049050036503000700801280300141003007400c03070600c070070b2003040c118080496040e140c41222056841e480c0c02100080400d00d81d01c6550a84a0b1b01c04106111801203030381e0780000b100304440c4c2e401c1580e07501010107 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 966403156 1250 966401906 966401977
    0x506040e0a1b12150c020318131512050f0604030203031f030c03030801090b04090816060e06011712092b0c06030b030f0610270c05 58
    0x40a6108854801c045040850788181801900201924407030b00c1d407425203600e8a6601003100ca13a0070b40d042d0341080031603500a1100c2d10b000d40c4001e506182c1d0040c0303212818614022035a00440c4042e0b80e208098420703811800445240d14203103a14140d0b508146030344400602010386241c0500382c0e5042c075014003c01c1d00390181ea0154000c40c1140c07506001c80142c103458802c5c0d5450810100400130025421507590001940240c590729010b600d00074841d402d030f0f14241c1da074034800d9107001580400507040c4415039807200d039502c3c0c40c50503c900320700e055001009003024100046c442c003400058a0b49a54004040c07030108c0205462012589001f801c0340b82c01804d01c80340d8410461401c10070b10040340c3d0041011001d45c0801d45441e500a0f0300e4012454980b33810541c0000e0310b904c2074140300d041c10469260441c00c007000034100b0b460020410000e98129000304030680a07407400c20074401c0d800120305200350740740c84820450014051005400390380406542d40130f02468551815990032068080030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 966404406 1250 966403156 966403181
    0x6010311330a09030f050607080921180a17160f0501050901120e010903080709060905060c01020c030307080f010b03040b040311161403060a050108031602180415050604 74
    0x41d104072a64514071a500a10203401c20022400e80020204840b06084041140258050b0507181015200203100750300084c200201e5500c640381d2107018100e0410490702101c0e05041d810385a030040c402c03011224003451600d07507121480050110381c8200c1c020032062015403a60841d607408140c00442e1582240354030503242c101617991400c201550007038000b4988404141340180c00d00c00207241301400c40d41e1030207941d02260740d603201010030507420600580d00600141401012507190580040158132240038041c00703801e0106074000c1c1040300350180d400e60f0350300760203482e100e2819142c01402c41e24100c420403800a6210300012b00346a20703400301e0303000382d4009212400c217a444ea2001e48101c4005480e511007442181006481c860200040501400c0a818601000e500d00c0303041601d01440507110320062494403004000704180042101c8480c50300d02003000b041c5105000080800700810388100b140f0007110100070402c00c4034048410340c1010040d0811450701d4020600084075250034200c0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 966405656 1250 966404406 966404479
    0xc0712112425094217101703041a0c07050f0609060702010c05030415031a010207182a0219021e060702030a08090315060603011505090306010311 64
    0x240700c1d0704168040da4400101d10f51900b440350780c01070030380c1c1100307604540048000c13091005415202a40002101c100440c182e801051605180e54030314005191842480e868083d03624101400c0c032021710039100100040004146001907005001345594031400c20340b0b0701801a000007103010714002111280090000c0c0c51681000855010b0001aa101032800c1c0d0501c920307607018000068040006202500c2c00380c0b04042540e54036003001e41a00c0ca00207a0301981d202035190031800c1e03603000411408643d180c1c42040352400040c1d5010005003044c061500e040040c6120a000303c3d415520099230000c0650300700c41e1041c440c4854503c400f00030041c025031140391241c410070000c030341181d900c0c0f205100520041c0303016599400a80742440254046940c0310b0302081e40300d464a414815114404800394000c0e0603460701d2800a0320360710050045030070003400b036500c0300078441c820b000741c84c42118007800315821543c4904003494070034600e040441c420041c5409164000742c006c404049586031143c440c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 966406906 1250 966405656 966405659
    0x402030607022a460503100504081c09031101020c15090709060f0f080708030a031806150e07050a0203041205010b0a0e0a050c071211242509 62
    0x1030450a00c83c0703422081d4441180c07004103910603002c02d41511800f014441440c24060514410207540e0a100044803c014900c1c004000035200450800d00640b910440041d40386c1d124500100640204200425440380cbc107401c0d01c2d1040e0403a8000758085000e91a0002400460031203079080c0d10920401000039080640c01b83c6d19000c24000701c0d600503040c40e0503aa007070707600c400901040360300aa110010090401c0b0003040a00342a44410000d0100500500b201e1420201d50700d0381c0c0d20801d2030790420075913901c290000384500402c14020340c55101c0c0c2e0a005030840c0030154001d800c074900031b60000e0031120300812049800348040710160410750b005141028600040804c15a0510b02c0035540c4e5500c558544000d5034500721404043c10420311580c40d141041c0c400c0000300c4000034030108040c10200042004100c4000e840c40c0d43d03103443d10f4100c0b000140500c146040c102c155010700401c600a80b54000c02402c420725440c03082d140e41060302402141d01d1074a1000f940205842008201c00e000f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 966408156 1250 966406906 966406963
    0x3151e0b130e07080a050c04060906060206070518090702060702060a27021302270402070206090f03010608010c02010227011704061e09150515040f0b10030203040203060702 76
    0x41203144642c058140e8001c544d5412903079080c0420180308a031241c100c1c1c880d00303140303203814401d0300c000d000940d408003d1713113080c0007010307580d410064a00002e2050108002d495880d0800e001c01c01000301038031280207800d210001a544032410b580c6040580141c0001a00001482c0b241e8111542c0b1090000d25020040750942c11550403a41d0698220480d1a8841d04020603800204441612400744403400948241aa008260192074552040d4010070100700945e4507207023030760001c1ca011030321030462180c000e00081c0180400d0b801028103508045d1040d440c150194090510784280a0b41500c0320717195042550068220f01b810316000c40c001c0301100f040798011240040c0e001c1e1182c41d00107007524020345160711443c0c41c154601c803565100c000380800c000a03070820429a03482458184440d0400044400039a4040f242d440d014999445900b201100c1c0d0360001c80d101c0700c010b4040d40c0301000103140280070754003c0303c3c268042d100741d0300410035076440040d01718070314541c1400c040400d590b0383c40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 966409406 1250 966408156 966408161
    0x120902030c0d1502040314100c02150a021b011a0409021c0309030b0f0106170f1609030b010308030604151a092803030201050705090619030603151e0b13 67
    0xc0103075400d8103030f10000c521101c000d100500c0614092450503072101464410075180400800580c0010f41c02c2000b0091711070b03000580307841d03000050f0013840c0007239444582c80c034001c0c0103510900380e401550310100c001050041d130000b2500342e005002498030003d440c041c4001c1d10f0b40618000d40009100d822000a50a11000e2800080c4689404200c045e40e0340c895240707806064035a03a60507045c0d035004000c25600050b91034180700429031000907915205141000b00304004005001c5203840318a00012640300c0d00a00003d90303449074031a8030950312030600c0c80031600221541d074000da1825644881106000030032800301d42807081c3d03480301c0c0712800c1019401134100c16849074104190261100701d081068900b08200d02880e54415002455820003e0035030300040d10640611204004041094450900301da4006640701c80d800011802900110700600080c3e0014083c210009440e0350401c90a0f008030703a80b100c401051011440c00440b5102c00c507160440803551140806504824004141c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 966410656 1250 966409406 966409429
    0x10f0c231c053403020d030b10020a032d0801050f0906030703060f0209040f0921140310090203010308270105040509090f011121160503090703050102070c06120902030c 74
    0x284034a40180b2040c0e000900383c4000c0301421405600300e40d0304503032504d6051140c0c145c05d01044aa241580060385000303901ca520084002c0c080003010a4041206400480c0760306100301c01c070340c41443c0f000d48014000c282080038080d05d407080c40c03680800f01803071412103d914046c41000300a00401803441e0b03200001000011001240d4a4084c018a0003558891181408032800340c103003c60f03400c145240004500c007060401c1c004a802622804a80c0c07903114207540b4032401403100b11541c0742c48854600c26004850360144410600000000c0304102e0f900d006840c0400025081e01d006e080b05800180080703071380785940d41c0007520501c010040c0385018400c1c990400c0f400380030b56191120b45400b00342540c9401c0e0101341604400142c036400c550264100c0b0402c020309410321045810320b84082c0116403880743c001f4081140100c040354440720280041c03c000c44d0b10000071940c494251030300c0c40020505110315030124101145540301e000c1240241c0c1c03035240e8020040d08141d942002045a00e0f0403c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 966411906 1250 966410656 966410707
    0xd0804050f0111070201111b011b05070305070302030d0809100209120a062003090c091f030b2410180b030f22050705010f0c231c05 58
    0x400e800d1450324502031042d43d400103041580c0c0c6a4424242c000035028444c0b248280a45900610807906111102c0f042c4412000c03003441c001e543c80d0580208030450b2590140b02070913a028038140081007180000d078a408480c404d4003030f2608940307a240c0036140b580341240c050038190080752401c15120150350062040140082103460940106200d0501d00504d106040301c8075680c0c0c2c00107d085024454140281c1c0741b080d40355078171b10315083d030895031030394160b6004a006000d508007284161044a112141103828140e11019079036a03420014604881910041384a11380c20051b600c0942c01d260500d500950003400750f629032010300e0801c41d80340112a0106150f1003000001003094441903000714003882c11840b03008524113140c404924101800112502c4040a54415a002490210f01181100c0c42401c00e1103610540074802d42c0d0220f00c3d900010241003158501c00044000485141c00e0078070507800b2920b800c0031400400300400c02d070601c0f0704080348080c07000360700c60300c010034050784580c62 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 966413156 1250 966411906 966411913
    0x5130e0a09060c021f020403170702040b0d0f0309093c06030809040e0601060909110405040e1b03030c03120a0605031c030c170403050a0e03070f031b080d080405 71
    0x140c0d4603200110b0f0360760120400180c0040302d04100700304415440c502c00e00c451500852403e40303980c2c2c42d20300c044146400785400072030124005007559510342c03242552000203002003810500504e44000902000c2d030084022800a010101e80381e500361207160003041c0880b90050f4017425150700c0400e45901c0c0a141c0d01800302e0302440c004101e0507406214002c40c45072658a440c2d101c904104000c3d60b221601102d4154442d00c010001d6035070260f075001c21a01911000070781400e04810303c0e41c2074411908000e03000303801c2c84000c0030145030004600f04110009840e00d0810800102015180d04c2110b460791035a6105001246c0d04618040341150001028800021466900c00c04241040503181410030303058041d8155540098041c0580095a1503900e0003020719a41e01035100d07404000a0000360400030701182106200d8020400c04000110040480c0c1c1740b40c0d50341d20320b03c024455034041141e03420755140c520741881032103424041c20745020f1800b500c2140380380b000880d086000140140ea0a10 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 966414406 1250 966413156 966413171
    0x907150507022115090105070905010f0e040603030e040b03060f0c0a02240115140a05031509090d140c0307030f09150e0a062d0909050f061005130e0a 66
    0x18110707000200c40c90f102c8090242c2503440104041e440704000d01c00e04160b418031080000d0640d024402105a0b04242085e1031028020f15040701c3d4401000c40441d0040c1c03502c9004401e05411000c120020542103805111300b034034560925454200580d154ae070340803514004150260401d101034101d9202038030480f20207801c10322201c1408541842d8146020380014010b20940312800382801c00c80e501c1381081e1040003203412900c1224491200d06c0c80030003a011021802e00840c4981c815003450005060000e11b00705110345645070300c0310001200204128102c009024800803054a81d0342040c00051030415000e9201501c08103010303140320007005500d000100f6911101d40004030b081e0020364070b01d2003041d845410320503010381640080e403d00c0481209000c0711200c1c20400104290b403003a542d0400824240f05981c2005103030014007440c0d04140401091101452039984101821240c81120300000d2000313560b83c0c41001c3d100490801100d00c01d204006a8106203900300000d040000f4504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 966415656 1250 966414406 966414439
    0x1202091302040b0c0c090f0402091b0c1c03110715200405010e060903030a2a0f0507060309150c051c05160f0e0d0c0b120f090715050702 60
    0xb607000b41c02582d00c00c0710100f036442d4010f00070000e1800820054903504500e0801030313420700c0d608a004000a210702000c0c0000740305801002e000b4405078140450154841440340d80864548a9103203050340014514070414246521a00038400841407601841e4030f00b030f901e5203407004020408451030050640704c0a80e50342e589040c2d1268660b019031030580d2070f150bd06200c0010206105140064407958090001c01c2d6556808001c8502050041c10424003108078404445a00c44d542c405401000d01051682024050075450051152340b05409603140c168880301c0513801c8a80d80704c00500803a01c6030300c034040c80c21030795401070000080d28100181002c610b50503c0c01c1d0819100486110305445105001c03480c8922440e000b02c441050800d00002c90822034010f150300c915602c6240315002c0d01040c0c005204104c12a0780240106014403541e50091452242c03c101003034035035501c0e400341000010100000403d011050719400781065001c2c110358007080780c1da0f070130a8100303a910040c4003426826a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 966416906 1250 966415656 966415661
    0x1208070507120305041a041809030207051906031404050307150f06180b120c10050405030a230f0d050304031107032001022b020a1703060a05040207020112020913 71
    0x445220b1303580d403a07440d0b080100c1512000c540700000a04444103000c180310000407044503040e00114450001285855070070100d00e00380035540801c0d00801c01b40d03581201602841c107004180ca0050f00e00344000242068000c0d86188103c074040d1a0350001e10060000400150300b21030f001201031400b081c1c4100c002d02c0304044551540c00b01c004030140c03039940711070385000d80107404002c2e200321622030b07200a107014420307200e01005501900ca800504d0b6120b503094017a80c20b80c0c02505001d001c8a0003480c0524010204a40003580225200b65014500c200042d000583c00400300c4a90301400019111450541d0543c2019200706c0034490340d01c0c00902480f408100040042d4016071944610003600c00134101c100c154141481d0440d04620075020304005c40c0d490700e0007801043c114400c181d10007024200c3c101691114001e14021403000c1c0d003828402c0c00b070b024501440084424400c45507580040200b00d2250b140c00a0201d0110446009050050790103000540c2c0701811460040c100034201c1c1c1304 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 966418156 1250 966416906 966416939
    0x120c0303030203100f0602010b0f0d0c0504021b03032e060c030e13020703030f0c0318120e0d0609110402032802040906030b19060f0311030115081c091208070507 71
    0x50307540b00d049c410301d4070703103000b90107090b8500b81e42da96078034440707602c0784e980000740b0b801307290b0145400141000b001c0040720030002012402174140c0b500e90800b501181c440c2c18040244034840d48120b980c080204811340c840c2001c0b5034568480036241e09407590250360510007590303840d40c8699036006a00c00100d1a00081c48401d11a40e00000c2450710f01090800325000c130240308081602e880c6480014030100410744611a4000002c00c8d25044e41c00811140403210840d0181c0081c40e0303065280411005811091240d8407803054030782c2401c006814401280002c0782c0c445c0382040c040c140c240416040b440700304510915440b002d440d203500c0b800004291a00c0c1c0d801210707204105030400c106c02c02507808071a0100b28500f4140078036440d1040d54005603c00340400f600c4111501c119024554003540304000b0340c004e0322003a11516550b03e00041d00c071181c9000d6600076003007018124038401e100303200e8041982c41d00401269003940c5130312808035a411100e42160f040c45407800109500035031161a0300d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 966419406 1250 966418156 966418169
    0x7260924130201030f02090a231806040c0c201203040503030f03070504090f0b090f01051f1412180a0b0408030415090b0a06120c0303030203100f 64
    0x544100d540d4004050050031045100c2031a0160040c00700c140c1d0311010194646409280c00301c1c0c0c014001000000a229400c1d44550002c91050b002962100e07901c501403a10342c041d54901117400ea00c0061088400040080c030f810350f07400000107101442c01e580050000b035454500303400702101541e1007091004800c1310900c40403185038a00011841c0900302d400038150b491000e1418589000f000c030b6500e02504080d04030b5240084002030340d4034407a0041e9001411805414080e50781e24055400040c54400b4105008440090001d00c44140314409075040369409051850b541c805010700051800c0b02e41c10020400c82081d02d1a020295000003400071400082048442820400d1407004003a4a000d010310a94000701c1041c0003152640c103605902c02c2c1c004e8083c9030b42c0d42d124603103402c1c0d00411840c000c035103a260882c8031040c841c5418a40e8071a92001c0001c22946c1c2c0c640c1c6400113007098403000107200720501081400064440d170041e42d040304000c40c0b110750b0030741c44c0c542452210b00180c1001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 966420656 1250 966419406 966419413
    0xb070803181501210c06031e060b030109050a09050606060d09080c070815070816031d0a0201080a09050c0f0607020307031202071a0a180803040609051203040e072609 73
    0x500c9841e00f401c130402e00b0002855680298001e16540e0741c0e03081002441254141035440b41c001a8001034000c4240d40441e02c07403000c10070382e0786036514400103400a005d2400694a840000351051200b4800c2c0780002d50400010126a6110342c200f00e000d0b80001c200d0301c502c0751038503000c5001444040c0981034000c0310001404c005402c0144a03450703c8075604042220b88070b0300c4203210b0345540114441e41c000900c1130380400400f846c030005401529000d4485000701080440c3c010300d912000c180d196020b8403da031888241d0711035110001c1558000303c0c014189401040300000f840c50301240001e803202c030143c115400c20600360000303030400445a00035190038880303034010503070154140990710141291640c0c07100d0260000c4001d00c0039004a02c0c03c0410321003d802c0304e50140c102c64806400070486002100e96498035030718000c050780f40c144107407401180c08211031043c020020040c5e0703040d030745200703000421075507241d4003150304101c00d0007040ca00b94213450020950100c245c8401e441151a035008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 966421906 1250 966420656 966420659
    0x6040b16050105090a03050d05071e03020a1404050102190f140d02152401030f0c05090111030a1403040c180506010806010e130f02090a06090e100b070803181501 71
    0x500b503d20090001103160000c05040c000a030f0084155900c41d0100d01c4002899a9504825540d05c1c003c01440c6902516420041103a15032540003007000c1192580d4829990201d0f0b04281598020b5006490140e00080d011846044642101040060051401d28076410307054581c001ca1b00010218003006800c000481071031150100a0000d08141c0590040814901203040810101141c4c043d5400340402c00b1030784402d0303841394021882d017a1103d40300300441025144043d1043e1702686a8601040d0a01300c1c113510340c28040305035400443d45841f40c48440f1800302d9049416803006000b03d88040c0c041d41d0114101d4580070213814824040f07800000c071801c0242c009803648100810290400040105a0400740c9a4401180030514007100115250b03500f09510801b034007404044135080001d1240020301580c0c03003a000310450300d0300d0581c40c2203521849290380c2b801203c0d01840d600d40c0302c1084071000041c445402142e05c142180101640b0207419003500d41402103080c00003144e107045500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 966423156 1250 966421906 966421913
    0x3709051612110607050a02130b15030c0f090607050d090303030b040e1c02102c030313030507030e09101a0901141b10140a0e03120606040b16 62
    0x38140151012a05250001d001990348180d01c0c41e0100c05140114000305040040000c10000b1440c10756004105000149135071041400805c0418062440703035507282c5091038800c50500440b0f004550301c5041a00d000c50b11404500f0303c0e401241c4150b0400c01c10444e01c008542c1c24000683c80f81410b994060099140d410001c082d501000c2c040c5214034940181209400301c0050103c0002060045000c0503001203103059091210300d1404401d824200003481b0718610000015001c1d0b14480807002060040401e001c5540380001c4804200d0000980c422502107409000a810180d00c00d14190301d0828041d0042000c0e0301c800e41b102984460b070074805000620003100c0a010301030340c0300085420b00c10b02200003010010080f0100c01c1510001858412170b045040c43c4000c403140308401c075503240c144000f0410042c454000c01d05901c0c0f44000c045410400d8901070b038a0304543d100010b5040c0400c174540c4003200d4802410f0140d01c15010000004c0340a11000070348404501f21a0180c5c910f542e90a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 966424406 1250 966423156 966423193
    0x304060905010e0306040231020c15010e0103080f0d021c110a0203040b2d1b0a08030f0907050901080309030f03070c030f11150403030314370905 64
    0x400840c140b0150f24181482c44d00d00003036440d4000c1c0c0458003040031542c29181034214003204942ea15820028400c5000d070500103400600c00c1030300e0641103540c00801609202c01c101001e0240e400340902000041000c2042100070b441c030311003141421071030159a0315008040380e01440f03a160340852040c90780c2e0360b004010311074560110300380428103240c0040164000d4507440b480c0607101000300c000c40c0e81540410b0b002c1320806943e0582d4060b075800c000203410425213422002c0c903054100610030301c003402d10b04041307000c3c0c2030075920010700e078150f4684d03610305240072000600407140c903c80c1c0c0340b00207203d640d860015402421803101940c0c1d11a140010b01d820083c1140714044954010408100042c2d00f841050084a03007002c607669540300549070a076440311285445d0365111681803011111100418001c4c42240d100e510100003402c140b40940d0f5103054201c03132410741c05511018681c00300d040d0080a200850300c2103140c2e50280a82c0c15039004580c040035042d2540c4c1d1181031a440c0d20398040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 966425656 1250 966424406 966424409
    0x1a0910080727031202060c0f07030207050d0309180c09031145061c0201020a06060b1c0513030e0103150e040606050a23010504170c010206061002100b03150903040609 73
    0x1744068202c41c90a40a400714038411100c40141c2030400041c1c800c2890701c04e0200d440071b007800512800f05804241801410b480280c050194270314a00c035098030311420a4401c202e50000c03d034403000d10fa0b503c0c6440d41019030704a400d00b00d4001504183e140143e4031261a440c0042010880350039194004005007080c8281c1f61408460f540c0341d54007442110303500d40010381110703d40620020042d21081c40102d0820140080090040f0f040c003501062404c0e007900502020301002c2c030440041085030140c0d500f601c2045c2d81d44040e6254610507100407030300c00c401e0458010701c1810003103400511542c0760182d102c0d40d5803014001158110a0100700101801036000030304044402d034540b5400c101070420709805546045114243c02c2030a0030b040d034054400e440042100b03041341c5c2d4112254483c40c581740c458414045005005242c0010b1280c500540c1320400880241d000740580041d10360007000078100000b1455241c0700e4050010704030303102900018464200040030b1030301d0340e2400d03d014140c410607 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 966426906 1250 966425656 966425693
    0x6091c0306030b06060c0a051207020414010312030b0f0d05060414011413030306090e030d0608010635190611031603021605030a0203041a091008072703 67
    0x10100100040b691070f080c8640c010344202d40c00c96542503048001c900c3c03c50a804018014041c1c003448800018a46000d00485402502c0601801d000d00b4841c031440c080074000200380b50400f00c000d80586200b40e0003000400409080301c1c2103070205000017413080310a04001c84056009408202c20494481081141c001c2b12000901c240006034480d03140402c1c004003881c0101549000c22002e151080c4c109500518501314100160f01c0320302c0109807640c0c44156100c0d4600d042c0710b00040c614105121b410100c550078040c00c00381c3c2038001c40c07208130243c2945001c030b405001c07100100282181840703000c09944581c0007070081d0101d51f180c880709650f284845019000d40034170402c08504941c5d1402d0b044a00d45150040c0d071611445880e420395007481b0806092403002144031402c0a8001004005850f4421415031504c129905101c0562140c401000c0d0401011081202c445000d141e02c40d0300711405062001a0b14001d42e00d050f241e05440c8400a080c490068007001481300c98114000c40030704 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 966428156 1250 966426906 966426911
    0x7031d03031c020909010b030108011a01090611070305010c051c0603030507020d02041806020414040605100e0d24051609140112110a08061c0b1806091c03 68
    0x1a5500041c0e141c1c01032548044910314004420300c00d118a60f4112000b00b03000404005084d61145045400b030b401c240980c044542c0780840020851480c0c0e0800848a4416912403c400341442005c86042562281411007442030341008000101c0078000c01d00d01c0080e55440715100c194100740800c0b1103041d000d4030341c4103500d81700d0248042a8090100e83c0b4143d01583d0b1030b4600945840414018026030301c00c0501c03950449961030801800383c00a1088030000003c2c841aa0080401c10040301c500c2d11480e070740107440c160030a003242e015298404602d10000d100790401c0c0201e444100e0606030b100304440209950300c5034071a45001e2840303103a4204095954090380106d070300102401c0e6641701c0c001d0441c880c15100034010700382e100e03030071200e0080f00c2d1036014000a0b4000b9410b0444d80c000140765004945800c1c005242811b241d40e40500c00043c1c1d040002c820401c80d2520151000c01410802c001041910070b0102d92408004281c001c00c0d43c403008286110004200311503161068004504050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 966429406 1250 966428156 966428207
    0x11030108030403030513030b15030c0111150703020c030d06240e0405040212011415120601060e030a0606060203070507050901121515120b090303240f12030703 70
    0xa1001041e20143c039814140165102091200c4d520459001d62004100c00c0d80d42003000705102203140840b65049082c3d049a1009070400015142c200001b4404a02e07948849041c504c0c0b42402c0200c5a0055654140189010311116016046034466401c41101c079803100020403440d882d40520303440342452080c04400354200d0f00c6000344000013404000340b055071101b020605560b1132031201001e040c403010003004000c500074070040c443c1500300c9003ca82074100c002005205c2c28409204090000f900c80a840941c0c01c05c44107803030749400010b0268243c801e100310b440014009208140287c21203070029501c400f40c6181c000c0c074200403908514010310f082d0004020380020000070075403c6a000c80341c6034120000251100c004c01d5002e40c03000040480f103500040b07242051055801e50750145a200003290349080301c8542d41d110030384913503154160780c000001030403120317818210814034014105000c0403001c20000b0440c601c0e07501800500e0704005003000406402c2190b00400d488564044031018 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 966430656 1250 966429406 966429419
    0xd060624020d02061b0a091809110603071e0309020a0f0e09010c020c1201090c0e041a0906160e041d0712020303030a110c010903020307022b08090a2304110301 70
    0x1c10311700c40c0002c20303a03901042d4006068064003452000c0d118080c4990041486030f5111006005411070903994107002a40680103418a042102d101c0c4509480d52041219120b00882e04800c030b0005000405550f120010010b070b0f41d034140348009000400707090b40303524100000501d2000000d40541c050b603141c20380006405801240c4203000c1d45080700d40700944100c039510b4034050000d20760020090102d09002240d01031030241801c0c0034a02845840c0007041c002a81c40d101c0350016105034030030703134800f2000600c85510710458249001d201d28280601e00f04520105040e03c0c1004200070090b840d21103014040c4608101560003001d06100c14400c13542d09401007912484098103035081c6617100c0021079480d9407450300726602c50982c0c200030094040340b07003002501ca0300482e070224410000380c1c041c00410501c4200c801c0c180000070b070b18175084d11a2503075620392590200480607041b1404400001d00e5903000c0c0302e404d58120440b16100311200c106c10800044604015100d80080340c18801401074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 966431906 1250 966430656 966430681
    0xe01021b0402030c1e0706050709180207080405091326031918060911090c0d0506010e04142a0301090e0111071104060902180d060624020d0206 63
    0x28250141e8006030382c0d407203035000c0c90080e100d80d03100100d42c898a400c3d8244504103140c001e004071405040200642e0b200c811089a000710341e441a60810020310040c403070f61600590081a855120f2040586425515008a500d04d071049440c0042d4480565554044c451419070b0340c0503003440041d90600f60351000203c81e4090202401540085641c00310108090903140e0041d8003500e80329201802c91038540ca450401341c820f07107104940c0e0b184032180360010703803c2030100140100881201282421011101d0800400004014a04105940002100544a84c49009003141203004600c0e010f19165003403d154102c0400c403031404008590700038000b441c00c0c4054a0545203846004940001100f000d1030142c045448842104400000c40c07008000e03903048000360707800090714103100d1240c0e500c0f8054224001c06484910b400c4034428400960701c0c00b03d01c803441d510300c61980014042d4440051144000381d038104a5405800c050104036540e40400585480e1440c4d031000300120305d040070002c0b20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 966433156 1250 966431906 966431953
    0xb0609060a0b0d0504060905070305071a2715032a07020303040608070e041523010e04090204020409050901020309120c1504020117310206090d0507180c0e0102 70
    0x2503e65681010404101554100800ba0354010040310707001c903120f0803c161240c140e03100315080301c14003940f010355038140801038480b44591070040c10f80c040700202e40500100302900070158040e120002c42c1ca04000400051030050a4100f10a01081108079095650002454095070800710900c25480140d400000300c81c03ea61071450040030640751544107652401401170819809401c01502d4010850065007a2007180c40e804a0058192a2846a02c1c4480c800d041014001005ca0f814103c207030a1a42000c03061610181c001488c1940d130752a41800c0300c0042c2c0745403099035000070503c510500f00700040d0354007a000c41406807500310301d80742c050740e20304c03040002c607010744007200004055a000348801e4946101044903140d4520701b50360340c02c6e0502185021001d5812002c1ea0b18000d9410101120752255800307002140f0f07001080341048908005c0e00f908407200d101d00c0e000400c07008ad000510045109010102042d0026004400b5220ba150040c00c0750441d03002c040c003a0038008040d0640032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966434406 1250 966433156 966433177
    0x61703040e060f0d0f0b04020901060c02010c061802130603030311040b0a03110f070f050607170f0414030f0301050114032502010e0d210b0d03030f060306090b0609060a0b 75
    0x41030024100049404da4107400d00107000b40f040030f100325050140000711180300d144200c40d0303841a81e0320380c0c01c15203054680d0400a40010501100c407c00641e0303075800581010380310040c409086c60f981e0b00003904906030043c1001d5071500d46100b001015010b0080b5845146403030f640c1801d103400d005003000107000e0110054209516406100b2840c8245403c98000111001c0d015030744a0701c906045003001040c5034122a2449003400044645100e2508070224030301c2248440c1c59504c0b06d010003956468080d0080e107131040780d0600d2401e600c030b00300010110b0341c410305609510b96151100240040b105110014040c40c010030800140000c000781894003c640d00d0000a42055840012801004070784040c058500c154142389040c2604104140a0b0f03100e02c04010403a076008a016071309480b00320780700035006281215034500290194101c0100d541104000281c070303075a03a449103001d99541001c292900e540f40400d200d0310341006410f0650225041d58031606840c40c1c9828a2440d10030700740041e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 966435656 1250 966434406 966434419
    0x61106090105010b220504020d020a1e0c060b03070510023306092809060b1c021c120801080f0c031f02040924060905100507061b03061703040e06 64
    0x240380036100b1000617001c4c02000c1c000315112402428100c000358070040500c400b10348040d0b41800c1005100304024500d044a41da400150401e559442000d04103c1c0b0085905005240e0080351a80380c922203c54401d1290380200701c5607101e201c240500301802180ca0210b1480542010711000100032680c0d00400252010040c550301e1100280340c40d090400302d1611f00c5031400c117a0703070100c0c41c0d90048030880b4042c66041240c90482010082c42d219000c1ca0441c0080e0000442405841d084098030001e00d180510034a48030003544c0c0b6000300d00d100414400c042510240148010300e410800600c008901000808014a6a4001070f07940c04002d10100e54010007218241e01e01201134050314001c001080051049a004c070407047c82e018019030486003105007002000501d9403082e10008104c0c1ca0107000805208111442107034035612403201603452039190184c4003400880e45040307800058050790300041c150304060500082d001c041e402d00002d030f88107000600203400320700c0210360030510840d0704 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 966436906 1250 966435656 966435697
    0x1203021f0207021306050102070b04030b07030518010f2a08180309030307050c0909060c030114010504050316060908070605041403010b0303040306020706180308060f03010e07061106090105010b 85
    0x1580042e2141c000025080b00980890200354101904000d0980d1401d03002e95160307646507040b0310141d0003640300141c0404400004524100d000b6480a500f00381320b105001449980c4806003400e590840002e840402d580d41c03250b0603402901d21103040416001c0300050104040c61400416085001e0100070840c003442c003243c0001b0004004580804102030241c0380c6405250a115454002000301180503100460004a9580c4c000c5084e030300c5280e02d4601c140c2180d08000c0d1550b5692000d12000341400020440841c4554003044011103147c40950000d190340d0500800402c03540055018041ca54440102445102c2e049000d80d0241d68017400c01408007200c0d540060702516848072046d4041c08001804000e000d101d800405141d030145609001c440d07040211100781200c909405000078090704041460703460500c802090031034000b000403500040041c2520b003058496446030b00441c501c85c110391216501031150030b9010f000c1d0700081060b51b00d400207218091150092608400a03031414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 966438156 1250 966436906 966436963
    0x5100506060c070602060108061b03010b0d09020a03140f030301140607080d060803070606060f20070503030a020313090b2101022203030305090c0a0b07020f10020303010f120302 78
    0xa442c02c1007020822242d10903512200a91a6a000c2c01840410301440c00010030140005512401030966240b03040d2841c0c1ca0502d40003543d800c00d2082d285035036166400000940c1d16100288051801459540741108604003414544011300c01948050703001840104064411219a101401c2040d12a1907807228545051031035880f9514506c0c00b05031402c41c0105401c80000040c0080610990007040040c0d00c900055136640d00d00100c0a0000d0300c61501c01606800c40e5032119003210740d004c200d402d003a80f120700207802d58000680c00c00050784081000503000d12081c54040c01840310520030005070b2021404520a03004880c2e15a030382d00b149200007940841d09504030b40f0440d103030020080000322140041e0030030340198070042d40001c4c24540840c0700b02d000858000d8042c8001400c0301001803400c4140181030b04941d00591744440d07942d51440e519100c04103000f030250080d40c0595500d40c10142c2c640c201c0ea00c41d4009001002d0303500109800030ba0002021a002070040c41c03081c4104070070b030f00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 966439406 1250 966438156 966438169
    0x20906070b070207063c03020721030b0d0c0614160302070603050a0506091801021c0f1b020d05092e09050415031106040b0f090406050d05100506 64
    0x40041c1801405000c0002880e804075026042d03c1e0942d440113103071030880380340d602c92100c0d41140c44d040035100703507251172601545070403008030584500300907080c10b045495602560000112126124215190b125411a4588100c01c0803810459440b5501c480e16201e52170400d420b401383c070f824811400520100e170300001081d109000c486c1d1002c8140c209551030700a4030f40e082d0307101d880c004c28240b401103400c2c2c021a0251910034200074140c0d000301d55540c40241145c1403502c05d0b074106950b0800a0007803680c458600d103071241500c050041240f1402d480000111620750060344902e080c0241d0504540342c0c0414035844c502c401d4542192101e030003000194480d8040088490048481800f5030700c135070065191014100725545071070a6030382e07a0300c05010075502583d1121094408103001800014102c0d0030000030800060002803c144d00c9550309034040e1301c503070160001d41101144805e4130b458a030140001400095880c0c5003001c0b08c66407001e40d5072a419070180062511580003940984568 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 966440656 1250 966439406 966439417
    0xe0c0f040509010b0a081005010813150e1e0c030601031b24031508070909110306011806080a021305092d21040308031f0312021e10020906 61
    0x24100c50b07655035100b4011100b81d00640600e8049030000b000520f03203a26130489241143c0b410385a8090680d00c030000700b00300307140c0c4410407192035010040c4400c1d880d2140c4a9042c1011102e0300034241c580d848415182c103441211400c51855000e070b074408007a0303240810003e045a41c0f008141e0008850085070404c06040b41d000083c0129074440d00080d030700700c0c091202c4c0d0740150f2510700304210354280f40b00e0000400d0a00071a10f00d503000000030805090158008150b550040384080000f244090000303003094005c1e03205000c0c01240c1115803160b04c0713081c07041e40001c0c074099008001034481903000c0b6070200341a540010a6983e41c0002800d0b4010070f018402458100c0c04204540c8c0c2070507003682c0040a00d144440741c00d80705050603101000342e0516104a0b010710015141c0c00d1034903590700c0c1c0c41c0d00c2c3c2c0001d10303010b0102c0c01462155a03044041c6400405107104402c00c2c4803151100c1c00c024507040d2a440485400340071210340c020701d49404601d58000300509107015070b0b80c2a04e00041880391054 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 966441906 1250 966440656 966440659
    0xc060703030b03013201050102030f130e0106051b0102040609060c020103090210050d060501111506180403051e07020a051c0804080706030506490c1a040e0c0f0405 72
    0x81c41e05c0c1d03400b03618040c914810300881d14903091007012100a095068110240652400750707000b0040c041c0d01c60002400f41020f81e40140783c0807103594880001d20718025081c1c0c0900c0c08a803010a80c0d01c0524203c40c0070714881000c64008500341850004001d0117600c0070301c100c3c41400b100245600943e482508540d01094002e0500305940b400d9800080203544901d1940408624002c00441c0a622445060f20740400380741c0145010f901600d130f000c0c09030308058055948022050682c401e00c540c0603010502c80c9000e07071211900c2d5807142521400e0f0340140c201c0140a081c04002110040c1c0e551302c48041aa001960000b0b60010b00c10440620800720f05405008a030300407600240d04400024100f058806650303083c042e030b8a600342031086250001c400c46440107401d104504101841c9004280d5025680001211080c004450f942c640c0380c00d10343c15035000700c482c00b042c8241805200104889507111044925180c030f0090140030141d0060301204900b00c0c0007645074032081150081d00c024050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 966443156 1250 966441906 966441911
    0x501121d0a0606060c050a150207140c0f150a08042406140a06120504020a0905040807051e120906040506040602060a050109060308040902033105100e0c060703030b0301 74
    0xc60560955031511040112105030500e400441c80c24891628038001d19840700c02814550415a501c820213420590b5540c1069802d000b550003040170941460f001c0b90044018040262400040c044e00d1154031440b2400746090102c21407420300e050046450360703c00792412441c0c580b43c6160000100007035100d0a001701c031101100501c01c0f0010b074400421242e0074bc20100b44802410103214640c0401e10480020645400c6204c110611a81016910030300c000c008644454031813010304100c45040d41e0a994020001c00d21a080000c200010f40380c2c440880c0803c0740100c4040c445991b18060010741044504020441c600651910381c01d88000e004010040f607107581c0c6580b4001d660340350459840d22100d0400c4000100540103200c2c6e0300c162500061054945810826075001a500150110410f00d06042d240384c4940913028034480d03200d80c114483c40b02010a400c3c01490701190b4109038606614008011150b018000b889000303282059440302d4594059040640050540c01c090a40550 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 966444406 1250 966443156 966443201
    0x1b0d0e1204050901090513080a090b030a06032003100c0e09390f09010e120c040e06240a030c090c090b072406050409120206070c0507050112 62
    0xc2210301400a841064400ca8103d0307995804503000e550046d03c58001e20a80700b00c0c0040420007541c01060142d06509000c008070342e49545803202c41d1300444400c4d07452540d9407010320401882c3c8054110500c1c0c01030b4192404000600040d0710f4054081e10100340c0c995640342906018001c40e0100d01d12400100701154501d811842200004e10314045984140c0c11941f0041c2180c1610900080c04c3d20b80700a00c40c05d00002202c200f030a54040091a414403040755220070007a945c0c210b9801941c0f040c03c014240d401c0c911814030086c1d9924052400a5420101c2000b040164015484400e1080e0b10700c501071020b110300114089034915000940003100c1000041411642500610b40304c4a0541d242400c46640d0f0029442034000c110000f00303400f43c2844151501d0020035035000d00d8000466000449a60754030004041340d90700c9804075004000720207001c000980601c22194010428200a2208425513540c26101c8405014490510803c05a0890862429845a858404040003409a24 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 966445656 1250 966444406 966444433
    0x1202220b0901021c0e0918031615112208060f010e0708040807150f0f0e0d09030b2809030309021201020c071a0d0507050a11061b0d0e 59
    0x1036200c0d40c030242c05032241c02a981494081409039000d26100d554429184840801c00c114200e00c01405000d80c40d04801c030b140f4910441803000709154245260302c0e240700c100c60714095240d542ca40b201111003138a05200c40701e00c2c1070103504580c05480f20158401c44800030071058208007500d9041001d0a11501007000341c0d8840710000941610720711503a10301d007540c8180007150300c40070880d0010558003091000400140c0303012160040740e00115000b080100740c01216504860081d24120081b981356800005801c00501c001f000441062034400c0b4094110744400320080c002400b5800d4107401d0b44021605100d0100c5801c101d899206010b04c0004a00c1c20b00402a1100600603840b070842c0b5414410510b03014404c941c068040344002d866100d1070513940c418001400c0f800c140c5803003410440b44c0020080c3d440746910500c2075480329030301c624810000034045c0d0418441d8800c5070f4446810b001544c1a424210b031084a9040c112a030f5610f82001d000c8043c1032401044100c502c04e00301080c840703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 966446906 1250 966445656 966445679
    0x15090303050c03211909020d03051810020321040f080309010b0402030103060b041b270503010905030301150c0512031f0f050f03150f092401090c0f120222 68
    0xd00e0412011780700c420980c402d000440d030315480002c0d07005110004020009010b03070090b1145121040c103003105d00d85a40b0200380c0700c00c0413075a680d0040e080007903030318903005c07440300030800341100c0c42d03030200151500f5594904000303410b0030040e049140110005003414000d402c44454410301074401d6450b540e407403400c80b028201022503584200e0410300c401001c0140208210034040707142d50380c00c00e0070b4160a081c080d00e0861000084640024940101342034409005119441740724200079aa40c2d0325128500106800002c0c0030790030400d290348400301080b00090000a44000340c038909a9a8450812610b45d0429001030102010131101c000907280080d25019021940288c92226503c4014001c042c0c607144c09038041c1c1c0c9540804008200342c2e440810820f0307031041c1c202d41268400484060903504240240301c040151050090040c444001c143c0112450751040c0d0801c00320080942c04080d0001c0c02c1150081c40aa602080d00c9604071140700d680d201c0d2801040c4005261500c60041300c40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 966448156 1250 966446906 966446911
    0x120b060a03091b24080f060405100503160f1212030b040b13050f130818041112091005191a0d05010b04062112030b0915010915090303050c0321 63
    0x113000c0e0701a021142c8038029070500d4400c82c192651203007a50b459004203c0101400ba100002c0c0a000c0130012540344c4081107162021185d8031142d01c1082e00c0c100340301301d10300e44642103040e28040d802c43e0000000c0103000d034403071179549030308010929107000e0012800403d0000360940e40611680c0c0d0881c9200d1a40d03001d5070140c4440e2091f000d8940d1040c2808a601d0000d00700100241c40411020f41c21040b240015400c0e4000100007040035810800e50900a0704a107000ca40301003100c40610050b1a810403110a1000500d10305100034648410000c00c89041000340491039919103a100c1440d13808040605803009004121003000c10b0141040b0303000700303541050507000c0c0d0718040d4003044250b04a040c05421044140000b011803089988007089100004c0181040c9a11848540100e96660804030b1180d1401071000540c00440000101108500d501c0032218184603642180c140340c4c4110f480c03083e00d80506000d42d640007040a0180342d84a000c0d845030f4044582c003200280381150700f80a50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 966449406 1250 966448156 966448199
    0x50420090403050d230a1b020a0311240f01051509120a05010606030204180b100f09030209040602091809060115090b04080f0f0105070503240307060807120b060a03091b 74
    0x70591034440b8000e07d41c041c00144a078050307481244241c000034441c0b1080d554a841200580d0380e01204441413401c808120f222141c012400b00d800c2202680d0701c0d00407180100400c0b240c280c0d84c03028800c031900c0c50740326000031a40200001a120440c1c2441042400029035110b0020003144c0c1d92814001d0094100740a4141640218490b81c0d40400d55030140201a560003040c80d0020849032034281e8041e90983c0c9200288210050008050b075902e1014611450040c5405a42d90944c0c130f04110b40107261702e40903400d18140c0f0040c84107440d80000c0581c15240c00d03c4050100301550841610b40351050f500105840340e00040100b903035500030440480c003151040454211415186800e801c1c0d8408881c0c50700003840c24070004a645040c5240350030010302c1003aa480c446213041c00030a00303101e0030340c1103030300450411001d20400303035403129180e4100e0740d0750712040010640700030001c0d00768460f1014030070805884a004a082c44088402420140700c0202600c1b6401e980742011001c4032120107084 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 966450656 1250 966449406 966449411
    0x609120d2c1b092403071d060406051c0b09030c0307230616030c05390705060d0902041b08010e0f3610050420090403050d230a 56
    0x40140d0403c5500240203013510100c00c0c0304000d0792804400c0d24042c0a64044d450b10500c031001a030b510850a00e07407900c1c503081c1604100c1e0b103444000c0c88203503492a440b0314000e43c20103000783e0451461890b02c4400b65480001852680c41d050011440c5008141840d0007a0100044002c1048482d6040004410740511038070b00709400c2400c46034803048100c580e0415000c900f00c404070518865804180c4040b02c40c10910b0509a400000c66140031003038030032001180c2e000405035801c000058400c10b66000c0c6038010040c0d681010041800c07401065a040310494940c41c3c03500031551182c01101ca80d040f111004000030302c9155004000e98420b100701000301d00c0f4000818510458900c0d00c0d4401d140801c00d41c0c80100203c80040420589501c111884858509440b899400144180560500c00d804042054180f604004203604132190300b0300c2c0308550309040405207840c0d44a11070390140d014140b00f0307100c14000c9007020103410070070b14100703501c0d0028882c5072110000e00001d900461802004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 966451906 1250 966450656 966450703
    0x4090e0304080f03121605040e040305221a2d071b06080601110a140a0c05100c03080405150705030a0b01080c030a09030e060a020c030609120d2c 64
    0x242500d038445c1244440300441c0f28400168210744801d090b41d1a01c101c1d00d00b003441d0a40d10003580a280c4802d44003140060303000140c1014801c80c4c21480700301c140e1009040c140c02032a12040d44003102c28815014031404d40440d04402002a540d0900e01c1620025803100d805038096480c200c1540c0708060448180494061006003911400b50300b1741a190540c13507046090310340c2401920460a0401c980d40e40b84600e400310400110004e40003c0040360380c0004042d04400b41c40c203a0130a8038543c101a024441140c00da62009902250360143d42da054206042584c446041c81d90400e881e4012101c040034004090080203544800194071480399040104410304032080119500340301541c82030340c1103000b80045114810540d004600003486424a849649054404140c040e04401c10b6000540c00401d40c4061604080c4802a40b049414001d401020350884025016000b11036190030082c1d540c0a604000068010300c0e0303002d030039400c1c50011f010395100010350360303803100d01e010050b04981d20010b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 966453156 1250 966451906 966451933
    0x622051b10090b0717070f050714180703180c150e12280b011e0f06080103060b0109180b030106080307020906060307140f030702060f07050d0902040204090e030408 72
    0x940e42a03d00540300685042d01903181c003610160b00140200708100200a548009200c4a95039003000740b00310090030083d480c000c1803842211703001c41c46600610100482c034080062a402d2a94008038a050008101c451021011079514408100800c03003902042e0110303480307413410b00c591291072442d990042004c80300e405003c5a155080708103035840d840a030315604010004240d03903046081f01d0031104034450458440b440b41400a0703000c1a92151001c0e00043c1c10b0030701c0060800908175012010144510745400140514014400684070b65a610a4180715a104815075002011403d0b0141c00d41e854a4a100c00180081c0518601c250700e00350000504078000b0054031021074004200d030000b0b5030740105024803640018804400c2040b200308034034065581c03030080c0c8403900ca01c1503156103e2410b820b02902c3d080001e012031840c03140d08010090419030010451345450140c01b000324000c4014030120300030340925046040401d08060000700c0b00ad200001070f00c1100e216034101c032100c412801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 966454406 1250 966453156 966453167
    0x908010501051807140c100b030613021f020102210a0c030501080a0b060406050402070f030305340201110307030b041a010903022202130302010f08090622051b10 71
    0x2c941e0480541d0001c000f60000d80650b00281d5017030580c102042c035161084021604101a01c44604c440d11350340c040062860504024180d401186150714401c40d05d690b03000a242d640400d0380f208001c02524010002c241e100390166840d1440c41c41c1702084d2050480c2d1202c640880444a400415161640d11a00d051181c0145412200e801c000f6200e0784240e138031100000070008207a190016280c1100045544891009080b050302035001d142c1c5020301440e0050a40d900603100c45a4460b00c44454035810a03c030090000b034042003010842c2e50798010700c059002d449103071100500b02ca004001c100c081a09504103050308202210100b18001b00303009021a0081107010007030005112950038801401e01c0a04612419a421f101c06440c0c0700781180c3c1c4c4107990100e80d550200360070781c0108000715608850040101d0303000307007004446071404041c200c1c2d4032030f002843c00700d1102c4a601032446062a407500c1e02041034018058400300d07107101c40c0c92440d00030200b00e0741d4002d40d0720341c0207a5812442134 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 966455656 1250 966454406 966454429
    0x180d170a09033906020a14030603191103070b090102070602010e0309040b0607200a0b0903330a02031005010c1a2d09100905300a090801050105 63
    0x19161074003a440140f842c0d540e400c1c1c4001d8555031109000f4200c029040880f01c05101c1030748507a0300940d48160418008090000c0141031664424051091118030340e008203160340e100c0c841c44100c810002036410102ea004c948441c40ea5014043c0c01004590407043d5402445c08030030030303001c03501d030250b94010490886456021111441c1c2041c450001c041c50907401c21010118001d02107420601c0e180c88020000701c42180440c1454401d00340148941813020098000b86000500709040c540404082a101c0720340035022960050900c200701c080b480c4e203c80840d508404c1c43d9030000b03686010f02021009520503110190609602c1c2d000055640c811320801058035800301c2c02560515282420703022244000d072001c0300105520107506030140c607072000340e10340c4485a54244000c0c20460306a6007407441200c140c0691f00d040c41c21540c04240001050940f08010401140381c071140e07802079070000c0e001003000c0e131500007000485400c6158060103440544445000070010f030f9a07030b01c04002005014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 966456906 1250 966455656 966455663
    0x150212090d050c1b1801090c170106020a0605041b3819050d0207030c0c090506010e0f0a0504020309060103061109010c060c022b021e0c09180d170a09 66
    0xc0703030300080d404d200c1003110b84e9041000c0c0c0070740100381d0802c0c14203040c80c03c00d80180d48099941c000c00002c1382e60140742d144580c40c0400e2480c441e5410004000c2d140c1160714000340c440f42d10b03000480c04004041180111a2000032040750480d0303214200c8070440d00103078900c8205440b000c0a20b0500c10400d078403007024200302034015483c110f050b88010f2522a88501e00f5024008184118a0800d841d0700003054071a100c1c1c0e40c1e01038100f100c0c1c608481c0d058071581102c481586071000b0003080366084040c082d070b07410b800c80b01e144c5043c40d00d00020300100b00b99002150094000b00038410b2030000044e02d18140c922444040c04801036100765005940205641540002d481142c10004076900d0760142c00c48040b031f84195064001424444040d038200e0400c2083d055542c100c0b071480b400e070305001c3c3d507005000c6482070350145484440c0076a500e01030030581611032504480030492031040b00040e103003a000c2001c10b9034140c0c003d14a01410704941100189d9003015008001407100b041e901c214009c0d01d40c13 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 966458156 1250 966456906 966456913
    0x40c1a0d0e0c0a15030e0601060e09150306130503090616120203030c07120c02150a0201060501020f03180a170303150609100305180f0706030e070b0d020304150212090d050c 76
    0xc0c04d4901130303100c1c000340022400d165840c01c090030000d009024050107400c0036110f00403150340140074455050401011030380424010b0195980640d00441c56030741290011520010401c9a400e00d00e00790300c51060314561101c40000c81424a081e040c0d9240c09590240108503034010b20400c090740c0b20301c42201e041c0721200003080450002510240744402e2000203180045100c1030b940d0100314001c0804000d0100c1c85008511505001e0342406440081e0000f8805010010324200700f07a42e6900a45c0700001428180007050080c47c1c40c0c0340c6146004101c01d094802d1076032141040240c587e8016a046585a200035010b00c00c0f9050a40c211403580c031010b01030008404401304101e004100c080c040590180d141100310000101c00c206564004036000d01515281e0310f0b00d00050200c0d100065510a55001500c0422810001d10b09031603540800c04400740e643c4c1d030b403880c001e10030b0445c60050030170312440424182e4210038a0410244940350a20480f11441000c0006550314010408884940d50 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 966459406 1250 966458156 966458159
    0x1c1e170627090102040e3d0b03280b0a0801111e13030c050f0d1a072f010b01111c09090f02030604060f05030c010c020414070f08100e0f040c1a0d0e0c0a 67
    0xc00c00b00003103500c8031003035045021000c606188242030405a012b0040c2c0551142540565890014015001408020b000700418491550080554094000c501d225000f0380303405080b02510210444008034100707518080016140d1501c0b01d6001584d01816008118515001541d800d00c15070000324203400c912103000b02d40c480b01030030304400c4005101c0000c00010402d001018564040030355000c00e240310402c0044224007110600b181c0b90100d0383c6042050000c482c10704014040b803003e500c1c00100e0005201c0380031004095401c0c110541c4080700781032824000b10806d44959010714000c180440d020f10200c0e80d0b45610115405003805041d916402000540d0060341c01510103026007440600b0110f1042c5842034801d00b0442c0803140b0b01c0201d41c00150400e42a5484088581c0c4191486a44200c66040900c2d54503544e01c01441084100000e101103000d000003200701100800b00c040c1591000b01003420781880d540c00805140f103840d810169001100031000c01c182c441004040c140300d4195 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 966460656 1250 966459406 966459419
    0x6040912201906020c10060909050f01050c0304080a0e1504030b0a0b15090414090d110307050304090c170a15080a051c1e170627090102040e3d 63
    0x2980403100c8401c1074480e0013040360310701d41d66010340d170010a00001c0003e0ba40240341016400d1000c2f0024540481c1d140004000e55a20203500f501d40050300800704a03203071100c002050740e50503420703860a54021030308030340d01e00f8401c070140c024025a44a045200344a0301e0b80c0884805a844884866034804004010801c044c440c64001c0e04820380c00520105912185c2002c0082c2845c040d070b51240c0d1a080f00b10120052a000300050842040d140010740c84c01809440319502c900940c02100b6463303407102c00b2041c64621a15a00000320445009000d290070314210a00c0181600900076920380049440041c01c914007042e102d154a8100014040c0030b5003801202036112481d494003002e110b684a101260106050f40d060580800c50715601c180f00e2602200080c40c6400a02c5507215150098242d500c6968607015200590466000000291070301c110315800790280703030800390741e0103224800c11074100c10901074110b43d4940b01c0510b24100f11413522020000018070f18480651108290400c5030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 966461906 1250 966460656 966460661
    0x1020706080703020d090807050705150712050705010509010912021f0b0a0b0d231302040c022401030209161d1908060609100609090506040912201906 66
    0x801c00e079240040c170340511500000100e504142065600040200e4008104031003040508050503007204d5460b04401c0580c901c940d030b40700319580180758100c4202200c040502440a0707401003036001000f48503516225904500900c0d1404054804440d10354100210a00224200c0100403001882034680024191000080c0540b0040c00e9000608481c0024018540c84040c0450640416010901c540040c0381c15076080d030780070030f46030010f6920410b002d071441d4425011046160306507800300b1102e03d00d0a007070b42040c2c804540000c5040340601d030300d09240d04d26011a03041e81c0c821a401a02911407601390f45041103500c180c2408695440c035100707843c1803440011000c07944020a60070581852200c01c4d80b001407141c0c44410f4540c400c0c424044d071490031804072075200141069181f8240d2504800a0980c00e0b0351083c0c01000756120082002501c0700e0b040708024903006803000c0141c00003418018000320129071002c2000c010018a0948100c2c0441e800080f9240751607454842c0d4650f4580c3c900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 966463156 1250 966461906 966461911
    0xd11090f0d02150a0203030a06140d020d060b060409021c02030f040b10150806100309080a180302040216050d0306030f0320060c031801020f0a140d06151d0102070608 73
    0xa01c0004524103d4010000a0080941140d194043c503280d0408660b00303400e80c4c0c00350300640720340c842d056007041c1192a00030b0a0030810b90102c40e00c4068400c07506040b030061603120221034015200140110380d9541507001042805010300b100c0280c0b1010030444000ca000540d6541d01c80700c48400810003203610101542c0d040010030685038039550307441c690120045c044c00c002c2d501140c2250100b000390310f07240d030382c809101e80c40e42030074401c4104560705c0b09114803500341c3c00d6050041a500791040d40e09400210300203154003a05c1150f64880c04d060300001d541100904954901c9111582c2090034400e0140400b104e51011003a5082c1c2001d0307070300f81e0344022100140101c0c5d285460303400340201c204001080c090790a00010640d40c0c00d100f8905248080000002c004987c010855a5038981051080b100d09191510b059442018103802c0704010703202d04e0394032070b100a0078900b01003101c1551103c1c43c04044090b07100c0700011502c031001c0740c0a5000319070b0348a002d81c00200c1e042000c0d0b03000b00b1207250b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 966464406 1250 966463156 966463159
    0xe0604020f0f070f020f1008010e0c0f120103050105010f0b030406110c150103120306031106090d020a030b0f100b0703081f0602030702100e090c090d02040c050d11090f0d02 76
    0x604002c0b088000d04199041503a041d02d40343e40000c50882942003040954002e903000f62804125040d80c103001802c03e035010b00c00c440228403804002110b030305400003941c1402d10a07040155640c0400d00e12600449400c1c041074849502e4036000095201212500104a6058020250039540e40d41c03642c40003400c103101c1304003c614082040d80b0b0003001c03e11010442c82950000c04a5950540c102940c51401500d02d52092610b442000e0020841d10120b000a01804550041d61001c9800200c0d05c11896184020740205410750044104900c540c2c4151007055000808049a5600305581170344215910941450b10000c00c6201e010a00c11580d1944c44540a41d061807412000d003c43c80c0001d440342e01040041c0c001242c40340c21868500751032845c0b03d00b2031514a80d20380146001904050340900301503408180081d0390078143e1240234607611134031780081c81082000980d48003d00550322040410814514140b5060814011003040e1745a091001d0040c80e06020100c0070700405183d4240180d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 966465656 1250 966464406 966464437
    0xd030902011419030c1110091406040c0e0a02091e1503100501110609060c0706090c17010c021605060706060305030301030614070c0314070318030c140306010e060402 73
    0xa042e038a60b078004152040d80f044a903a5025000c01c001412240740040003401c010205401490004002420102c5c80d1912100094040c566190209030b0740030720700500304240102c008200c18407441451003400c840c03030881c1c4814140d032a1090b40d0304070311503040e071158010121015070603c0c1d0901d4020700c40701e4401070010070341007010001c07100b001d420464a1a03400d0310454410702c41568020300f02c0c03544620784001000300d818016910f07a00c410307004103104104c10011801100348002500460350150b000705c01c0021485d2180d070301e404a0340520066040310741c01c08024056452001039400024400a120100801c3c1804c0070481c2542c0107100c140c4901c1c0d211031010004c05c1090000b14001c40c42903e00054040d881111b0340840e005c010018020701501081d0003022039000700c6414a0b44041d071408580c0c41c0107030f14094441c0c030034a43d0034020315607800e28007108212004466070190381d600b401d5040b104020000b01a5507203001d0146d501ea803a07100300410243d0030240c0140001d4030102101c0c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 966466906 1250 966465656 966465677
    0x6050309030c101e11070b060117010f050901230906040b04020301080c0118030f02062a0601180c12020a030207021e15090d0b07031107150b030307050d03090201 71
    0x10b1440c0c810380c51650406070b60303241c2c070101289030011000c207041c030122a424000000102e0302088640513854016142420120000300c13541e00c41e40c416040741c401d00c0064a40365031102c11a041c2d82c400c0c0c1c0209801820118008120001100130911400d9980001502040201020300200c08030180074603070815114460b08803690741e02d0024501030002400107101071201c103400103000a600450030a003e64110f0f5080c00819456003038041c41503010740f4240e03618820782201c48501d082c0f83e10803880d450003020041e103d5000c003150160403910340f0340340e00c0078801030715450310102d031000c642c1d000206203618115070031041141c0140100703c82a080c010304028494010800e00b003403007147e07036503001d150034a010702ea0700c0c1039101c001c1c01407410b11005040c4a40740000c501800421302024014a03040000a20304074429044420110010b18104d0303150002490006119408100d0a82c0018182411891303a820004280c1d40c070190420000d007450000c1600075001400403410503810001c40354071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 966468156 1250 966466906 966466927
    0x90e04050318060415111902010f0813020607080909090c01090e0a06030c12050d030203100e190c110613050703020d0507150903050f0c130b011704030203040f1505040605030903 78
    0x1c0622405e602e0b621800c0f00064a581c51600380b000010640f00080782c010095405070761f010950856180c0076041c0040a502c5000034441d002c9800c100095029500189e841c8c01c20207034030054001d00f441680e001e81c0c541c071490300c030980711107140c0c4805000420700326080014600b000c1c4190f801a012000010b421038483e107816014a20507000300400b02c424010100401101300054010090185011400d60500b10008940d51015101e03404041600740b022520404043d14503910408042030100440c509000c80a008050110140c9986015020000b0b2290311548181001e01e548800034041071811642082030070a0210000e440d41d228401c4d010031180425541c3c41020302e61a2607403000a0700e9441c04c035180c0000c1000e40000ca400110103556a5260044680c03c602291107000c07074003800c4100101c1d008403803110014002c852101c1448140b41c2c0100c000d006030b1355108480095541c85a002410001c100c00c4000c0015504000c20041c41d88250095070f00a10b608003600d1800c40c0302007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 966469406 1250 966468156 966468179
    0xe04151827050c09161d120607021e0c03030702040e03040306090803060a0b16082d0702030c010f0f03021602060d060e06040b36040c06090e040503180604 68
    0x307801c03103a0754008400e510b40ca25007500080c0d0302036442c068941d1209440400104004540e0313a00644461000d91001d025075038000207403400c2d11031641103442900d4140c000965824045a4800d0034082000122030241c02c0071440040303484010b0021403038840258244001048c042c405c040544c00140310200000d0310a0083c40010380c01918019224101a401c100f80410250301c061000c0070100640c0d02c405d8090189055090342002d4040d071203c5c2c0d020390380d100c1c3d0350004a40f40209031102170002e202c415070314050460140203804032010050900019a40d51020110b141c000c907071b841c007002c074106121b5001400321803c003100c0000c2200c100d40c086645030f0046640341c0c03241526070200340443c3c0031040c456a0702c03c9080b101130021035024400700f02d428038000003191341e00e150381d810306225988403800030b182c804101d0384050b202c3c98541032540d51600309006080005661403000114012a010004e0140741c220001e145041e81d8200350107038000210015035000f00003480006005003004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 966470656 1250 966469406 966469481
    0xe09030405090703181704180e011506080103140a0602030a050a0f06050117100503060106021b0f0117070c050d02010e01061a04150c050d0e041518 65
    0x5002103444034101810010b445030010b00b030000f0107103440d142032050032400d607040c0d44440d0420040e0b0b00c41111803a580c51030b84070b642c1084624248010850015a0f01540016210481c8000802c03403845510744440b590700882c0f040c540007402003030050011416000d6584010107400c0c2c00c039086075070306a90b45000c0e44c01c1110440062540e81007001525005070041d0b5100078003104040060300d007400e002074005182c2450300c400711444c50f0300103000d000a890080000d040c000b01207035030703541e51220000e40e80c0c1400c00700340c0741c0c0e105031000c0c203182070400103a4981c04580503110b80a101c070f4481000b44046400911102c1080321500e1400040784090068049404d40ca50001c614441d4203610903080d1906940310050361000c898031000811440b0094034207403980700d90a01c01200700d000d81203a8480c8250030103000303070042c402c0c0c0b03407081d5810080004440e44141d81c188040c900703c0740019000c502d907228110461248050324880b0031001d500082c6403101031258000301386240c1e90313036040c01c01c0403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 966471906 1250 966470656 966470671
    0x17090f150105040513080a030902010912050606010f02070f1205010207020901030303061a03011d0624071a250c061415030d0c1b0321120204080c190e 66
    0x42c001400c00e07000341680b0048040f00085100d101c0d9035503016600c0b07000601c2c0304050ba9548100110780c4204141c00080c0030404030515230b4a05800c110780c5400d0207580b45804980340d4030601080c41e00100b00360045a004012003202a07240075010b2540c0f2400800890b45550708221502c0141e0704e080c440e601860181e0740001e1054240300d0460b41a082026000b20405410700041100b1a4462085050034402030f070004143e80b50f44d40031486550a881100300e00c3c00c0d4151002c66501d600b040500328a030301a584019080000c0310101845040c20b44018180c2861803000c950b01810005c0080641d00b00da05c1d080c89804403503154403046400c1e02c4c9241000c0703801c0e03500380810341c0101a070040c10140c088014015009404038003410701810210020408000c8250000f6041d03ea24110345c011030304100c9505904400086941e0035642003045800428840004100119428400d6405a840c003000801c02d0301c04078410412a00003000c074102c3c0c0c0400c2e0041c046462184c800c00c841c041e450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 966473156 1250 966471906 966471943
    0x90503071101031b66050a110307120516060c051905070b0a05070605090106120f150912030e1903110f1e060c1303060f1103090a140d17090f 62
    0x19202200d00001c0344c40c10b0070b000e03c0c5d580c5d004660100c1e50118840c0c000580c404022000b4910300d2010a050140c40d80c04141c02c00d20302c140ca80700b03000000c01d0408503001c6540e2481c415035102d070400c0d242100384000180c620340c080c18006240380c0e64062114021401041102c055980c0c8200c940810360158280500061021030501d0410025000d4990485c1e4087c0003401001d0030300381e1041d48400028009000c24089080c20400d00080043e0501000c1c015403080c0b182d034065003041d441044401141e6000646000036824010342c011850075500400b002c0200c00110b0581c9003220030803501e0300403038a81d010320b03051400360240800c80344030300100c0d454040d14600042d10441d41815002011143e010008001c003510343c2e0301200c0e030007099a51103200010507070130301c0f4280ca006055002e24110020000802d10005000c00035071031580a02c1110f032080c0318080d4403201912249480910380100d651003850f068a028821200395000b03144100f251500403807e0710352440d005c416906c4044081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 966474406 1250 966473156 966473297
    0x6091003021e090a0608030304080a030608010207030504080d0c11040b0f1207150c0c0317070b09010608190c030b07020f2e020c0606060904090503071101031b 70
    0x50120021360701000300c1404021007031810340c8a98503403000400007045c00f8000a40a54801d0096008001811080c0c00071500c4409910700904198010b00401203d4403c40803903d41040c82091019121755004075a07000d040115811710010301030700300690360b000412031041402520392084a8001058800091820350310780741d0313a94121889080d81c641044a0000d4142c04107402034070000850f41d010030118030315040c4540728101806444c000030300c0417410100780040058150803100070b4582400c03d446103403e94080c900150105458002c1903c002c024040002c1100240c6003907101000d40192681c80c4410001d6a00340360200b00060703007940000c640355414440080f5401c0e0304001a020462820a61600781556403034003c00c014415180004c11a05613140d641001d0740703070b50f8060100c03134686043e4a01442001c0341300c010700703000034544900045214042d000150503605c0d01d0b152000511605039680401023487c2050905030b103014105945080744081106100020305800c000c40306 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 966475656 1250 966474406 966474409
    0x27060318150b040e0d081906080d03090b24040209030c030609010e0601270b030f0703050a201f0e0a030f1208100902092b260306091003021e 62
    0x1508001160100d95000500400ca0709400c041c8194001d4409007e0100640c14443c40c0d1028103050f80100215000b11258000043d401d50082c10106100d420000002d40d1821100200340440420700400301d52525060b0029007080c1d80100421030b800341c25200140321420100b850510156800d0889a54070064000725260600006014004035255402a504030426504040e90540c00401031650780300c05090160364200041401c00f11880240c80300b00360740b0305002d51a50518441a02c1d440c0080b513003040f2140366120240c207950001452100002d00d28800c0415490502000b41c05010182980c4e0600795541d0a04000441c442c3d100c0c1c404440039494210300100510445006000c2e0140074820403410241c40302041d194080001a110b40d00080020703800811500380340800d0812026040c0c00c4107186c295280c616009201290451200003501402100078410f451600314044c40804c00515001603030a030402d0b01003106140241d145d4000070650340b40307641e0140440c050304401d610345 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 966476906 1250 966475656 966475661
    0x418020d021209300a110d0f0e091303080403050405040501090209010e0906011b03021507090807080c01020606010309080d0c02100f022a1015050127060318150b04 72
    0x42c05070706130442070506016815000741ca0003c090181c0c850401140701c40c5058419a00c244c0321003a4881180c0c4a095181806085070b50b01c889807500043d81122034085506083c2c013824040c1161012000000000d62001c03500c600028000301c007000010440010240d6582c000c0f00c6c081c1595800059498111200151641200c040854000c181400400c4042e03030308401401182c2411031441e40800740340d45804c071308003040c1803004042d1304803a6040c0a00c007640b04003214107540c1a0700403945031079111044550f5880300f00c001c0306d0050b80000000f91040d4880e4000c2c2004c1d600c542d10117418102c203480c546c4103881e00c0c00c40d050300581c0034a0781c48080c000c150056128244081f801145801070307012408049607551105420401020840802c5e0840100416190903240b843c0411085019500191041030684502c03030008012183e814101d0030b602ca0000000c49141c00e981d01103074582441600644102040c0c90031080c028404640031841d006404190104c86800021355102d400781007004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 966478156 1250 966476906 966476923
    0x305011d0c011403060a090e060702010c09080307032003070615050a320d0b0405070b03011d0403030f0f0b04060f03170309100e060414030f0418020d021209 69
    0x2268030405000180e0b0341c01c04107600203001c030200303041d55941d01c603800b0405004069101c0b46500e0720741215640b040e60b011400500030421a8021f2142e80c034040001c40395440180120352464004001d146c0000f130142c117031003149030b044d0008581c509400ea0300060a5400912041d40c019440b000d100c0440c1100c2c0c2281400740404440340301060b418041e003682014014104111540d0900d240b425000c10400c1a807a00003200502c01000c10700740c1c3c42d009612130b00903901101e01e4458040301260f24800a41079078144e0305206140b01e0002c5010f404140100001340c0150145540c80e02500d944c000036006202850201c440c010407508580c2090004450041d44480d2004c0d910150600011300201c1c0070503400c7c1180740c842a1651070780c40c2501d0402d0400711982c031407686807031444288407901040d11441103004603503007007411001030f160713648a1240102410203c0c4003000180402c41c0c44032003052203815401c2e00142403070a042c0440c400c0341d10130a041e1952840e400b080084000040041a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 966479406 1250 966478156 966478211
    0x1e21050a0903030e0f0a03120f0203190c02012c1201061d04170d1406030601050319031806020a0c0f03020d08071b0303030f0f060e2707030501 63
    0x203150011082008040728050b010040412848600381c0c4416917981d440030f00804001400c0c028090381d0b03440c1880d0b001c140100c070800401c0d072103100100128008400c2c1c4031400c5010400720354903031807100d00300c8207401c2c1c445080b8103003c000140b15010030490300400109540d1000d115a030a82c03544200003a40c401203103542c4642e8103240c0c2c14080e00300742c89101a04003102e8282e502042d00c440c0791802d00e207060784c07a040300d80d8000802d45440044464011600c80120600540015200d00c4245038403400d0074016241c042d03000b90b0010748074403032014080c1c2c1910b000b40b51001d10118180c000407001101c0d64051801a8444400c4100b0701c215100390314024034074040c480042c1403969000c0384d000218190082c00f5035201169040c00e100741c900d040007803d5030034051400c21f20349078580a8000e01c0036042041c40d443c41c1400c2c0c0403070f8800a1040c0400d4500f01c180101d460b40c4d03018820743d0031440c000180d0300c00c02504ca54444c941003041044070080d5100c2d40001c9000360079440311880006240c542d81 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 966480656 1250 966479406 966479417
    0x20c010b09090a1e06140a060b07050c1002010b0d1a060105180d111f180f051201090c1203020d030204180e0f12070b0f0402060d02071e21 61
    0x660b90200145544034550710002c40001010001080b000d02d0b140040080c08043c1001002c5440003030800e855449400180000c1010586035178980c010750150351030080c226400458209a94070340300c200710825040764800440c0c144588408941c5002c100c00080f2400769000056440c01d801d004501c42e8070590038038144d4280f8409140004540d070618490750b01444240b1400d0060244100e07010b034a4030800340255500f4842c540500c03001000040d089000100451000d9218130345409104003101d100070803983c0d800f8180000c00c0001003200c8081c0180351340e00d541100000e8840041d16001b0600144406030010311401c0c0a4203122039034040d48201481040b091010402e1042081d41e480e0104a0005d100150943d4070340c5880a82c0350206100d1180c0e042c2c01840d141c4000040071094801c90810f0516140c0812444042d4800d03030b07000303500203070511100044550715400741c8840341c000d021704460008944070502024118174002e80b0054210300652184131a00009100745100d2071404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 966481906 1250 966480656 966480661
    0xe011107020f040f110d0f05092802030304050a0303080a0b030f07060e13060807080d1716030e01020309160e0c0405120a080a050c0c09040302120703030e1608120301030b01170f10020c010b09 84
    0x4ac0e1100350b121042301140280d0800c4010743d00c0801c180e0300a0200038003000c40032038403410068005081292581c05130750074a02c0e140141d06003c15840841001080202441420080151040c02c100d811190300041c0005a030905074415014020090100384098100c0c1410290380c6814000e40c020448140441011048681c0030403180e40341d444401160940d00d416500030086001d80891000c6d42080d41c000b00c240140b0f0311001c58030605144484142e03203903056880c000c409095201320342c41020303e0800d10040003542022000150388030707100400d03039810380060740d40c030903194101408440020318041404001c040c03082180c00c08030b50b0100c450711014513280d9002036071030a0303111944460450100b2070000f05400f0340c00c410f030350000040c2600d00488184409041040040c422119544980d00c60b0f01119003444085030306981d000307051800c161f8200343c140d046400c200800e100c140c1c8254912881c0b03014051282800030b0708044000343c0d55504c48104c0d5030941d500003c2c464400c4c0c802600307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 966483156 1250 966481906 966481933
    0x9010e0c030f06030a0c090b01110111161b090c030f0216060c0509211c020c06070305120a14160215090a080408010e011107020f040f110d0f0509 64
    0x640b64800c0366800040c0043c1d441c90702103410300146000040803940380755030102e112207080d00201108031080e40c0e031601800c3c1d0203007400c1c240d9101029815070031400300820003482c08001003e01d0b940f4007503205150058980704011800a000b45d001404141d42c41e42200c50041d0305020302d648454032081c0640c18070940030000312030403802d088010030440e91142c9003581e903030055082d2200c4241c010080e00440c00b2100700f20a0380742c1901099406409400d0821803981c001203600c0108000590040420101c800117021203640100c0e0198180141030001c0b44003142d52402c82440740c49510008200b03c111043c5e8851384040140c401d64112008076403e100e03180d400580d00340114047c190039026500e0301c00d20941040188900908a10000034000c07503603001c15003203c0c45012013100200099582144900300a0084030300003903009030008451629403406411840c0ca13080a02000500380840007a0f208481e4041c0074280b24054a0303084140c022440c0d44640360388584400003505000c41d4804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 966484406 1250 966483156 966483181
    0x1706100806071d041a030105090303240612180f0f101104030f0b040c080109080f0705150a0b040506030a031e12020307110c0a0b04090e0a0813030209010e 68
    0x80c00d0400300043d40d00c202440001c251540c08002c500900b04000c1684010a25105a6050817546001e98240b1021403859400002142c2c404e40c61021001c4c420100200000c10301d044580350158010f41c240080412041102c44142c065820040c4410708410b4a4184c1d13820701c4c40081003180341d0303003141c240c9107049540801d0f2000300401c80710000402c3c07141142401124060b68001824107140503a180702008400000d040c05140a00a0281450707520b07041c0c0d5080c0c0b02111801003841b20706120403240200f820000d0114240318000f41c882d00c643d5802c0e600d003504002c84441c0903080d280c58010b44541014411031360080c00c290058004041c40f0b8030b015104181a03030076401965034103a01c8100b00307441030b01d50200c0200c006009560300d080599000f40042140720788008a8040da80480b2401d1038040e1640c0200ca180b042c5d2942042d150080d19030040500d0210804540100056035000581150040c417500c2c88442401032154158010b000c40e101d03050700000603150604e01404413001c00d40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 966485656 1250 966484406 966484411
    0x102161103060c0d0b01021014061807051b1905030406230f07080f03070c0c12050618010e070b190c0312053c070309031e0203040e011706100806 64
    0x11001140c8001d8040c0100c2c60410315481c00d002d40e910f000c0d00100c0e6031049c1000c2c0d501a0004507084840c503601406034021900e4255510804504108030583c1030075841c01c10748100481704400d8071145256001d442d180341c140810121a540c0001806000c266002800d12882c4807400e0004e01e01c017240001c1200840c40f6060508184040105030314041059034011198000081200c164aa0402600c080c1803052110411955400b4000000c07a60200491140c40010340042c02031803d5203a4209a1481c2141b80c0200805952640703078015a00ea0700700704040080c0005d1500d59610320400240214000350019140704200c0c642914001080c0d1046a03204501d40035a8001000c0d221007203140022080420042d03ca144140784248020b40c50a03480c400070f503940c09420200d9543d00400b01c00329422204001e0120b143c1e000500d42044011000d0902c6091500499140c1a1a6001c11100d80d6090380b00c0f40c00e00101061444100700203000c86030300303c0d8503c400d00740207900b04100151580d000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 966486906 1250 966485656 966485677
    0x20d0c023403020904051c0206100e06030a060f021306050720130c0215160201060902030c041403010207020904081e13030b070905041e051f0b030a0b030102161103060c 74
    0x80c540403905016050044543c40c0c12028010141f064080c003000e5112502121141c10344604080f001038004210b0300614402c00000b00640640c600507039401c00200400f52001d41241d03424098000300b940d800c003105003c1c007290380764152030b8401032a01546040c40341c201588110210010340d8007640310780003d04074010062038040342500e01070500301c4c43e000314180c00000884450301807040c440502c00c0c801e110300b030040e40280503880e2520140c4041e8441a02c004803403030000c11080141000c007200351401c1c10300050026240002d0b0b90001100f215003031b03500755504a000101d544000502e518034081c0107840070080c90406e41010440350030390344e50380f001512035403215000500b200c1c4116000809000b00600c200301c9450050032240304287d013882040941d5280c0741c046803c5400340c4a40013500c49103d0b1113001803c1c00d0456045150f00043d00110840d070711206500d203203642c00c2c005040050f00c061402d02130308400d818140c40b8008020a4140250450804c2c403404840c48800c40340c05505 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 966488156 1250 966486906 966486919
    0x5090c091f030f15140601080f06030c0d0c18021b010e030306040216020907050a020f0303190c05070c03290f07030b0a0b07061d0304060207090906020d0c02340302 72
    0x90f410800d4899416801c013a0b22189440e24010a41c10342d060018020b2030300380d0310241d0941c1e5440c5195180f107416104280e0692119209400c1b52a04c4122101c020b4807601611078015614845083d600d4451400c0a00c5076401003007a500049a220281d4071041c4890000d1150074045468aa16807102400080c000c0fa00000d9102d03d010407400e05e40d00c0694045c5c4420003904d040c684c01052078102072800c00041c0103040c518400b4550010a5a0188420101c02c82d907403a40c0c84c192038001c0200702182d4051284c00d00c180c4011904d500c1007100210302600148284c1d40e00350000c08234024441c90040c103103800c1c02c014881d100710014802c950149c000d090001d40e0312242c0303000072011601540000c1b01441c002940008020706500118100c5c080c25402206000b880d1a14544a0045000361001680121001c000c6019150060103031036015036401860484409040010340b070101800c031016920a40c011403204401c002412288558581e4030300031400c0a00c040401d41d0090720000c3c0c425074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 966489406 1250 966488156 966488183
    0xd170601050d09120e130b01120e010623012c0405090c0d0305040e0f04150b0a0302060a0804020f01030605331209060a1104062105090c091f03 63
    0x803541c001948507401c030f400312440c070500c1078000381100c10400042d805118900c4146c10b5a030000e00030b101c4900c5058582e0041401c1e2840d0110050000d009030b50354a649a400c0000d4101d1008002c8140b0116400c540400c2c041540000d00350701e01045c010700300d804802100002528242c084000e11210440d804221520f8088480d8a031500b83c9000c1036001c600c2c1c00d010010940c100d00100126000c0e40491421940d071200001d5952034202d801a02d007040c43d4004111003a02c1c2d41c89028519070003000c0c006039544076004510160025803201010821100a10013036241c0230140d002454024a418030440b0704100c007041980708420300f0414040400c20940c0458220100c2654000703113103c11842d2203044500b01c4071218401511060003e0044201003640c0301c02d94040e19800c0c4000c0800203140a160a40403620740420a0894144501101c04034022501d240100f0740a0301e0208002e00c50000c0d40020403d8050303009c0d0405034900c10b00100d0080c02c40d010404d600071650017240004c2403e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 966490656 1250 966489406 966489427
    0x70807030e0307120501060e010302010c0318031a09010e0105010b0f0d0603021201020417031620030a03030c020c0f0a0506070305040b030103121e1403060301021b030304050d17060105 81
    0x101d140d20742255040c01a4000464814540c005101c0001d00400003071202c00d03a43c3c4400f00c400f010078000640010000c0200328042801100c10710710054003001410120f175901d40f21035802c4c160161200c1103a561920500c4400c600900600400c0700600008000d0307540340041d00d00091180f01e410052104d00841c4031006d080207580300000a42d0082d121001511146090034001c0d03000c0c4c000c00d40900d22041216040c00000400d5800c400c03104218180d11803440e40350381d0741402e0061018820400e40f1002c56010f52014401c4140c4c4a2103074802003a04141c002001c0c0c10401c0040559000c0c0203c000035003083e5480c110404d0880d83c0075511a40e0b40c280c0c0c0c1c202120280b1564101c0414071000100001c10881540e4202d61004c41e80c2d61003084405103040d42c2c042c0e0a00d81e5070b4000000d84038801503040300f41c980c4011900980010001460402c2c400410306500809013000f500b10b400220400091140c01e01115020b45aa4500240101c502c65141540d400c0d0107421241000320119510180b0f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 966491906 1250 966490656 966490667
    0x709061404050621010f030c090207022205071b2a050d03020d1808061513060326030421020312010e041a0912030a09020d0804062307080703 62
    0x9868040d140e01c0c1d5800c042450306610300d044c0ca98500c1a421075600005580241c003801c1130036240e0000380b00c1000c5280071101000382d002007a09903408841115440e03154904040355110b40e010100001c40c8610308000c0241c03403180124020030303040401c55018000a10032080d8a00110056590300881d02511101507406080c1600700680011000300d424042c1034000506c0a124181d0356140840d4404664842586003c1845003c007180e00880114081414648922601c050064642c2e04600d900101c14001c1d502c41d275106441060407400782004105581c040e122203d040c4186071441c40c00e096540c02c03c1444200008540c2d13010319400b840a1500c2442141c44c55003d03100c0e0700301c40b540c48561114502c4001daa0403a00c944150780c00308201010b4501c40d40c400c2001c030020b0400c0c0044415402c4480e80003d001605a5990300b08810040e030318001840c000c1401102416141c50410b00007404e240c00d210032103200a10304074190724003d8942c0b021030340c1d0315a02c80c03007940d1280404c3c68140c0f80c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 966493156 1250 966491906 966491909
    0x70f050c0f03030705030a0c1b08030901090c09020408122d0d020d020d0b0d0302031806130603140907030203071701020d141b090a030201081803030f06090702060709061404 76
    0x80c82c000007080c004803903401800f45000e140b0b644410403219070450000e40c0c105ca0b0088030011078400c4201c480021401d03190241d40c2c040742c840c00210b4090a0780c1e44886a4040c10382101028683c082802d1002d20010024000140d502c030318900d04d440c509600540071340f60700030300d80d00c032243c8802d0650015440c0007080c0c0303c8013210100c00395120740000382210007a41000d06c00f2654186051020b00c901d1412080c07000300c00307030960046c6203080c8012001e40303140c9420b5606250412402c0040481100f0989900c8001b445155400200d0711403602d0f00c0454104090034245644c0c1c8254014409681c010400e041150000d0600704d8061100b02031141c0a40503a42a5400307440c5002c0e40805501d810f8404030b40b0552594a011071541a582420402400b810401d02d42003104c811013400154081c00c030558002c02d260800f41c00e5180d4824256140d54001c903602200c0c00554014002a41481510550040103500191080d854400c0000300031a62030300c14901000001d00d115841e074400d9a04480 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 966494406 1250 966493156 966493183
    0x40803061c0c06080606190e061b0a1101210b0f090403081902040305030f1b030f071a0105090f15190305100510030318090207060902040b09070f050c 66
    0x12000722a41854019500d4500c50000800c804e10001903451601008031902c468840140f43c10042c000b440456107042c3e03840000b038001004010414440f030390f1019440060085400038446a811454070368031099a18009a041c030010903945443c542a480138820400802200020344c0d50f49580025001d941d081c0c1031030f0708400070340180310070306520000503442800085402184842d007440003504074032981c840941140c00901c41c5403010f8000308018075461840300710b40034900041c01040c80c00c5602c121a4a07001040c00101181040701c580c2903155907134016008a5020340c50b050100e000030000034504400786103040000340030141c0b054241003e452001c3c05c07022420100341c4c0350000b40c100c0c0d80000e81e1a44204807141c40c01784ca0070701509105810b484030408002d45141d5040d03416650880a018072486038007004141200c0c070384058000035004241c0842d40b21018018481115a80c844071406000700e40c040089041e000b20048492940320f01c1d00d190ba80240c001d24509080c8482c0802 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 966495656 1250 966494406 966494449
    0x80709030611210c07140c0a060518010306120219170f100c212304033908040e07030e070602060906270d0f02010b0a0e04080306 57
    0xc0711550b04140150602e81d021881c1d003150580c40e0018240d4140084070701c420000d10800c0144002a0304c0310285071401ea00030119584440d100c0c0006840c00c21580081e000a10007045520300703240d0000700307041ca40f002030030704001980c146102509280c3c0001006401a9800c16105d840a10244100002840c0e43c40b103401500885d1034203151a01032010150009106080d01c40030000c00510500719105c4040c1c0741c0365400b402c54003610312406014100d0340d0310150b40d0742d1010100e015040580380c0c428130500030700000c0c0ca020302d8083c00e031a03030500346c22400f80d0b801c003071a4406402428034158040c0d0740a08c140c0d1045500d140c1400c682c440c0e17800581800114006000e48580c25030014444038806c034081c0d130100794544104130390311202159459225071180f4040b800e840400100001c81d801d0108201d1040e0020602c0342e4079100c410302a000029940683d010102d5a0a1086005428045800070f0801d4a0070301040204440600090005100000440ca0310340d20944292180070203400300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 966496906 1250 966495656 966495671
    0x17070f09090c0216060e030c010801050d0f140d032304050601060e1311030105040b0916031d0a140d0201112a12190801150e0312040e150406080d0807090306 69
    0xc040c1e842c03c0d44014003911406950608c02e42c01088070606880014002a01440680c1c58544c0745c03041ca14030584050754a51050300d4481030601100d4103480c902e4801050f13180d1480308010a058503030060006429904060000280d001708005045401c9480c01c2503504602d14002090040b440c22101c085520708061080300c10b8815020b14101c45040700e082180c3d907940014046018022144240f41d000124841506107010754800040c0d954034549601011483ca030b512072904001001c01d45441e10403841c1e80c05d2990041044909420071b0348028070400314404a44001400b601c0b00300760840030070350b144080304198400e403e0f4101642c0d904a800e900400d46041e0104d42c407091540c0110132040c0740780141f2031f010700d0034141224800c000340e226003280400d08840d0300c220341c103107241d150043d842024003e15054003d00081c0440c40d402510500b0442c880b401000c1c031141c20340340114145502041988000714100944e040d803401e1120881e961140101c8030bc1d8019000180b80900e44040f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 966498156 1250 966496906 966496919
    0x804080c030c1e0d140307141204232d03040b04060f05040b12090a06020d24050d08250602090f2b0507030b0717070f09090c0216 57
    0x10428010b25003442d06180070103069001c141c45840c40204c0502040d2108403242001c41c40314001d650103080c40c5000000308038509220895503120302c01c00244e10301090184803e1003081628490040001004500c2e07004280c402c42d84c403450002c0b003180b0f2003540b10900d141a0031540c1310640c0510038090507669180d0b01e460032035030b842d001030240100243c0c0d000d43c0348a8160203041164155824480d500b0300700326100d102c007180c2d2403000300317694014082c0ea03034003400050285c000303080c0210300024049070089101c6140303400ca00f682a070380c04588030b914800700a1500c0300e0800d000e00395080040c05998601c82850710714030a0600c11203086a8081900200a001d82c540c01b40010100c201c5002c4848074800341006000007090360b100518403d48510341210f5000420740b50b03003c03481003050f103911694070749580e031481000b215004082005081d0384030392664020760b0594045224101240c0d00c2c03126030700040052006001e0075865a40d81c1a406422500030011161420900400d41502607240c80 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 966499406 1250 966498156 966498163
    0x1090c0609170f10180b2d041128030c0f1d010501030c1b14010c0206090a08030a110a1806020c1309060207020a0b04060f050a0f0804080c030c 63
    0xc980303840400082c44050500e8004580c64000d03402100040505081c80b0303040e44000c1030034400c007009010b0031995034000206825083c6100705014900c24041d4080181c0040c1c0b000f801112076020254070030304010000d00106400d01e415401a00ea002c20080c041c48561030115449200720040700e03007580c1c00002c00c0360800f8808240c40d04101c0c0204030320fa480e9a00380701c1110390141c44030200060030050096510075030003e480c00300c4918040344d00c00d201074206d104e203c00d5a12f00744d034038240840384045030000c00d00507403040d564184024101e42c50b00302d40b030b0f9850347c403480f1303006025082c000040b40c2c2940302504408100701c10703000043c1d603400090300050720b01c54460801c0c0100000c011000108140045072260800c03801804040c022001c16640c2c6006000408046480c15402d00c040340240e180d0400302d80203080c1c44401150340c0c030700707209000d041004807000c114204881001100580e9a00c540d240000b040302c1c0c1042011604c8600c1c0c504024041c01c06080e10910021030990190344000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 966500656 1250 966499406 966499409
    0x403031404110f01080906070f0207090606050301050f0901060f2601080604141c050304260a03150501051804090501112203050706050a050702040f091101170a0e01090c0609 76
    0x1210f00c1c030540c003012401903d620b0700855450000e81c10580004421500071045403452815034416624426100e030850000c031480d9070001c0c0000b440c00302c0184800c2c1844d60040805403422034044804d503141c150018030044203100044100700c030038440b48440c01c2c1ca500ca0041d51b013000b200b0700e090540c0c5644601d0365034081103900b80d881c0d80012401c1c2c000b0180c00300384108446080c0d161600201509902500c2662020b44119070180d0074412101c0343c0300030010182c80030500c4520203551261140001002e0700c01d00ca0a5010f50203c0f00e00410a580c1c1200484510070b02d00303811038802c80d89030700000c0c004000e480c401804950910341007510303189120004003900d600504249150b82000b00d81945500341a00000300541d001c24814000c0c940a03002400071031a4074500545000d549501040940e9044042218604c0d11440f840c0d00b0043d4042c82040300b03100a107040a00320122034140011104081e080e4881c03156194500942080207400000e0f035a5003200c6480a8a03548040c020b05180e100e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 966501906 1250 966500656 966500659
    0xb0403030e130b011e1b03050406080912095401050d03180b0c0a0b0703090c140a03080309100b010c0c0311220617070f0e040303140411 60
    0x203405a0003000c082030720402040381c00603541d18400d515003208204640f00d03c04e50040502003903d0420203202c4e5215a5002c0c6c29201c6c2e40c5454841c3e1500e4000b809101003c0c110b41010307044180781c1c00c959240c4e5415640711420407240704a80d0308407040141c80b039040d407000c0100d1401940015a40030305942e084070f58904000364000201c1200002850400c803030a006141c1c0c070121034510704001c68866400b034000d0844400c444403400d0f64807800e03400c1c0e0f0360020b42ca01c1260b0f00190b410340203010160740f140380d02044505081c000450a55511003040455000d490540c83d07503483d001000351034242c1184055a40206410340d281040e040c666998040f0205640300700f0301300703940040c00d0351094090f219141d5221803031540903801c55564a000161401a031600f00d144a819001100010000b50100c81d410741c0d00000d00609100300800003c2c21031003002099404040100104501041c0c003030101c5400001820240d1100d203801c5010b888030703242c1d007a041c1c02400c00f07100a0051740b2520f4041400c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 966503156 1250 966501906 966501919
    0x1305090a020316030c090908090607050c010813020607060509030c160302092a0304030e04020a11160501170a0216120801091802010813080a03090c090603050c10090b0403030e 77
    0x1a0b642400d00300da014040203150303500c400701c104840c100d160424907d191040c48020708240a076000705085401500080c1d1340e650060034144181c0d60080581500305401942d0048281d600b42c010032418851108004c0c00719a0720b20004a07400413b100361150800208140c03104160403100c01080c0b22524002a440340c013101001c0380c408260a884003840650701d8600050a5444550300001c0d81c2000f003055080c02a8500e22089643c0c0c2d5200520315480341d40c0700c0c80345442280740c0c0c861070f01c071001030040700da0000290140b0a5a8000703000d0290740f000c940482045d0343e00c1110b40000f1f809040c52a240b1491840c0515081001c0d540c00da052881d820b90300d9800c141c0c1e07600b00f00002e0b01c00b003e0f0012071200c10301c60b40002652041003041e41c4490410070014680e01e107652a04003541c454421030002a544682e200d003007107030440c1070100924650074240502815174030b45070741b1820703580f82107440b41004200600701a070141003000010004880c0c0c9940b150b580c0d04001d8200c0300020b000600c00c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 966504406 1250 966503156 966503173
    0xa0207090204060801120804080a0b010e1302011418150316080613020c0102090a0308090f0607150b030f0106090f2304020105030c091309051e0d0e1305090a0203 71
    0x100e1003500c003200c065039070300ba005034605141050303803043c201416187c4600c20403011414440801c01707090040e100745040f00b8590715250700034642c00720240c030035041040d84219600150380e101c1c00f045000031b02803c0480c0c2d51400e480342c140880705c10100d91608160050b00280b80d480c10349015520500e2003544074424086054011203c0020840700ca40d80010048940c2c8800b40107680034201110708074000501d40320110000581c404410f5000301c03100040040c00c003142d4200500214910300068500c0c5041c02000d5880c10b0410804443c3c1e151550b5a55550405503a4101301400f05007400300c1c02002455100c2c172111b40038091041f10600c3c42400c000342540c98101001c2c0410904641402c11000c0d900c584d0300448a40d0300c0542011070050050000100c160b4809402081014030042c0024040c01586081030401c000306605448403130b0403140a510880707021442d003600b0b0000d4505291083c00c0000080e541081e8a15a10462442d02c020403114a50008402d207409000724100c4c2c00e0f91 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 966505656 1250 966504406 966504419
    0x15010b121303020613060e061006030c0302130b0c010b0d03230702180901021b150c0c0709020d0f230603030307021b03030c0303040317090304050d0b04020111120a0207 74
    0x21481c10001030050303000d040020803509032000d5160809114400229019409426880c030703020b0251030302907001c1c424910400c2056054401c910502585007800e50501005040703a07022900c40c0d200d10102a0f03000036120110041c2940034454203000104100800307481d9040042803101e00411088940303140320300c0c07900c104d042e01c804d980f02e056000380302c401c142d001d901c00c0540078600501036100540d005d121092000b91203401d0307154004144001000541e12202e0302d000f00840140ca0200c400a0820201c03080300c0e000706882c8141d540c0c82d80c015a65010641341d4000030400000d40c80b41840c81c2c03407025055800d00403010180c4280e00a160541038031840200740e1688801e850410140e4001c48001c81c88403020080b488001038028196424580d440d000c07203055500032541140003943c607501c0e000c054a000424180c03c10009070003141402d050401141c044884410064151811079001904681c0314403d00d0589098110542d0741d0080310314400122500000e038800c0c0540198000407514 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 966506906 1250 966505656 966505681
    0x40b070206011206020703090e0a0218090907030f0c09140115020d0203181908030909070c0507050d2603011a0315010809100c09170c150c15010b12 65
    0x42e43c0110b11810200341c0265501002507005200407001e0000008000410032035a804280c03154041603400340c4e5070310b000c801441c00303014244d82e083d21640b8801c040c803102c00000641c19054070351003655030842c4c07086828200304145142e40300c0240b250501d4003070002241405030090489526800d4080800c07403602d0260786801001c403c0c000142c0c0284100d40041e006034820000380c0e03a014040810f0b01d00fa8110f81d2001014503080740070140d100083c00306050800c01a1680c2c0040b4030300d022a2164490383e0350544070241d5200c0c0900c151039045110040c000801000c4080701e0740d40102d200149008121202e85030001d10560302582103560a04019140380c5040703070b00c82d500101c3d4040b44074400800542d1100b4003d405000d031442100329a080f8401944511107803a00c036922003808051500c40030b81380c00700c000300704200d41d40c0103407a0340c46160f203c501c2c0c0100c1c203610000c401d540302d00d544610036141910306407010781d601c80c144000291400f00e44009100900042e48000034640e1210a02c001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 966508156 1250 966506906 966506909
    0x5090a0210051c2315030706051e0307090b1803010c03091502030c0c0615030607030228030b0303270f03060f04150603030509040e060c04030609020303070c0e040b07020601 76
    0x401041c41d280d8800241c43e5440443c0e6215425443c0003103210f01d4030340307102c8800100c400100c13001d90b4410f4410146410800103005024a1900e1880c2c80ca200201c15003600b61745511245034400400881e2401d4000c40b004009815001c0c40a92910f1040b09a80590810340030036034065480d00759843c94141c8280240d80c40540c006020b105084c1101440d00025840140411400c1c8014000003010341c005225070350203100b01d0601d1058415070501018103044000d440001418810081e484180c00001d280390000300380300042c90090041158207802030300d0f80c04040350341800009a007050003c0200c42e4604004101403040900c610130900380700505c0c4c2c00d035424980c9680441c0c0004c142001090115a0161081c1c0d1125503101d040d5840c142070710a55081140400c00118030f000590400384070b402c80c0a441c40c4004e001c6030406d00708000880c4614003028290702c0c0c452100109546041040f20013666100c40000d00756940c4405440b00d141040c1e504a031501c1c4040701042e00184005400f50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 966509406 1250 966508156 966508177
    0x1c060614040506160204180c05090601090302091f150e06070209160905030d08010501030b010816050729011a09010f110a0b28090c030f03110105090a021005 69
    0x2441d06080604020558000d42000c0342c1842c20b610038a00143c0b0345001c0d442d0b01c02e140117421b8054401a2900b40020146500024003039103d480c00c02801780e9000e01040103c9030140c0d00d40c1969100e52855032031482d030000c0700104480c1c2d138030750000d00e04407442202c0300685215a91403400f2508a01001154800c04401030740c444a140b01041c4ac0206401010800418500702130301c0c42c95648010900340040c6038601030204100c04010480d03035805001e480b442c031409180600707151a1880f42402c442d2000001d110030401c001c42c260741003203a56070406800000545049150f80a1010020000c1d03400340240d00018602c1c94005007426200c000340c0300c50f100140c41c2e05a4025800c00100c91626100c0d48281452064000d00d4000c2075085804500400308082c00040410784005002400c0b00304002c54030f06207250024090124510300d60001c2500da014000c041a10254101103c4103a0400603042e0103519003403e11901a40c0000c0b0a44003074420b448850002c0c5070400242c415004080524 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 966510656 1250 966509406 966509447
    0x22060201150f0905070507060c0203182205060d06050103060b01140f0301060509040f0c080103060501080a051e010e3a0507020409140d08010f0b07020102030708130b1c0606 76
    0x901c0f20740999044644d0007141072500341e00342084c41d180c5101f595101d0303911f100903800020f00071200c103041401801c0d1000061320020303041408040c80080100c130104007401500c0e52640400c40700c1d40d9403c1041c2207030340c0042d4140115612803e000005044010170540460281141c2075030b040140d100307841c208040c012640782540e2800e8030944250f480030060f6a446503544d200080da041c41427140080d03200442e03940910781e40c1140f60100c00c07603406800c0140706901410403000080c01c00510400208084030301080c104003007100b464050f20703c0e10581c0c54240680a901d6a20510010f03a00100d61000d0150b1800310310720160050190b540424000c000a40c20030800300581000e4115135062803103210a5803409500030000c0c2c1c04d204483e4109400682c0200c010080e44200ca40c2c84805406908d42240c41c18100b070b4000b079901c1c8104c0b40018a0700300003088540940820708801c00003400ca8000442c5c3c1c0c3c69020040340000c10301b81d480012410328208010411900c5540c01140442009200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 966511906 1250 966510656 966510659
    0x12f0f10050f012304090501050f240607060902040504150b01080f010b0a0903050319170601020a0201120207020604060f021c0e151303050a0201110309011b060222060201150f 77
    0x586a51000c0c64458858400718130a01c0752043c1c0707645c0f01e01c04440b8024000012581001020b03141640c1c0c0c054180b500d81d009681000744600c100050059240c0d10445000780c0d00c603414a032060292401c1c08010b54041d142500304003d01442124004440d203000300c04000d03c2c1030740e02c019651a8404c2d940140d242d030081b00180500c0103410002d005074102810100380d20350380c9076500c5103194040b00c000c1c075030409108405d141e80c0390803400070b2501e5085106100420b00d4480f000071f40e03403600020041e0401552102d1000740d0b1400360304407014250094680da03a580d40300d04001d045040075095200040c482c104052041c0ca20030840b824010116a660b98210100c0c4030400031000c913841c20444d0040c03000c2003582051203518000100861080b00a0006c0701c0c0180000b401e50080c01a2600c2681c000b001100c101d40c0c1d0011034414000021076001990114a003040300082c0203403c41c5c0b000c0e00c3c21031036903005000b00c0c0c00110002c03511b155000740102600d551002c040c1640a20031450410140d0340c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 966513156 1250 966511906 966511919
    0x90a09060e01060c080c1c0f0314130c0b0406080f0123130e01140a1401151d04021b01050a06030201051611090f0103030e1e012f0f10050f01 62
    0x9948840034005c98040d03007801d00740e003280e81c10609085155110100a0b04c014602d0f030340c01100c4400d075000325081c100501e03d000818207021460042c126103056000d400b40d20100075a404c00e4001134040390200b030362074944a041c060400c413004d4030500040000b90b000010014519030a81165000c180176440d100102002070009502003c0200d50280e40ca5059030300d5091400d111f1941c8002940041d1102c45c04e10310503000c11181c1e034103000a9240c440c4e0303005200020a2130b110303046c0401146051012a102c80c003c032440880d01c10110703a40503000240ca4a050340034a99407110011500f0001c011640710000030508a44051100a0200d40144890f10ba5130300c0342c012803e0305c3c50141c03008040e41c402003030009640a1088402e4102050440014001d0603407112102c08180c1054a806410681a040f0464042007000700c0504005020142d254840003e02584007580c0001043c10501000500c03400d4503694445041040ca00c600c00d10821000c4560261a008680315614121140d09040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 966514406 1250 966513156 966513167
    0x308040809060706051801141302040207140a060606090f03030810030b131412070213061e030b0c0901080c0d020c03030c030402010e240a021f02090a09060e0106 71
    0xa0096809000a1011007240e0700c449000b000103501c078a000181c2480d1900065419044c2c1003602000d680c0341020805201c05600403050b046100807808500d02c802c1880060041e115140c0b000b081000c400c00f42294030030740010884c41040c41124140078242e02c440c0d0803160041c20b4400c420003401101c0c1d0400c003090003100781d15080100c54035145500da4403900c51088190084d280c1d41c94181001006c9000d002002c500301449171a0003000d080815040c0c41848001d0091034006803042103150108561a60b441c0e100d500284080742d01d4405804403400892942d061601c81036a64141d100f000030100301410046a080c0f1105849030001c5807516184003c8d203410107000f16642c1c41d42040104510541000a107108510910f90b403503592402d44001044818580840340c020303525011000070381c00c0500e09034461001108001d40c0c0f2032500b018105c1c50401c00e03008652407035030f004190b040400e00030780040a0502056402d2890266554403500c202c400c540300385213210b40c03080014080640f154 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 966515656 1250 966514406 966514411
    0x2060a0c02010f050705070c09060e0a050a0e0d020303070f020c060301270216020a090209031506041503060c08090a111903021c050601050402070804031b15030c0e120a0308 76
    0x18400000d00000d500b110000715130003914442d010400100310541048915a403180140c900c00c0c009000c628034012409107003003009804240041d4a6500007015994036a01404842101d88100c40c0c0c030070002c4501035104d46c41594400001540c038528203100d6400003c82c03910160340a826580f55a00e040d03c0525000035001146805203000304000e0314041190002e00051032880c0341018a8030350034030411100d006207522a04950b0300501282c51a9940031550076807060320451000c425941e6200010010504114801c26040340c0050100c20b100c1da07075000c400b820205885025454030390b44481592152414002008035401c82035840f200d08043c481000c01c20200d503001e40c0e69170340b40d0740000c050300d070b2500c1d03505c1e00f59070401000c200b445800c103c241e0041c04213a804500c2c0c000a5122494180f2960001519072410340e540c0101c210064100b0000521811800ca0b5840c2c1c103450b40100a040038589000001e580d000718604a0f1502c0031549604141c0c000007400c9501e050b80d025144500c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 966516906 1250 966515656 966515681
    0x1d0306160203041509050a051008070806030304050a03030e03190b07230304060b0307090203060d061d061006031103251e0e04061a161506091a01020d02060a 69
    0x3c1c0000942c07510748030800b1015501d00c0d1500030101d0300705000d1151000c0164003a030b12403202001d040c442c86030131455032034202c00146842062680d681e80883e00d5031243e580080c1d0082d4408400200340740d4086559580038200b00c05844000611002801964888600241603c00480003150b140c60140c0203400340e09441c2461411000111040400c941c4c104a5040c0c46c0300da11a006000c040c5000d11200c07010306010003046003035040880108584035200d00000340031a80e290561a800d828100000d003c00710f41d54100d40003031078108821300c0d1f070510500c2858042070800c407000c00e00e182c000d015a44182c2d448050a40301c1284040e1092514a4084045080c4102c06217190200743c1d00c0900120601c0068540150703020741401400212181c2d40d001110310a0110184c400403803010088807591507090b00d0b154256565420b01c2e80d25a40801019001c06103000070000d07007500b04c1d4022006103c0b45424450700d0005c0040166102c14454020f080141c01c10000203030f081170b0a6101060a144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 966518156 1250 966516906 966516913
    0x1020a17093316140a0e0904060617061b091c030201051b070f03030b010504090513060b040b030c120c0d050102030a06060504031101050306150313031d03061602 71
    0x9110011070700c01c0640118110448200b010080030300c1e082c480076038100030005009a0041e030704090043c042030745040d21003074024002400d500c1c2e4612444218940a0000b01242030500345850070380300424440c418200654401da08182e013035100401c0140c03081d001007008030410310000300a405554403141c101d91344520825124081e066814803066076543c869000050241002c240d040b0031194031040389034030701d00c0400403100059802c7c880044100c0d41802c01258a62040c0c0c010780b260b019903000b204400745004100548449241030215509004800401041038500240320a44980d466466010b5200d40703501d41380c0b424402e00285107060030009440e41111024000307038502d01ca03903405440030381d00802070180c0514144141c1008061504241c1c0c5064950380c0c844280407100341100c0d06200c00480064120b40f111803903806030441019100c0d0b607074904541c20070108101c8050540000c1d0303042c20211002c016104182c1140c81006000300700c4c0c1d0340c07800a034180440120003a03104500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 966519406 1250 966518156 966518173
    0x703050a12021605060f0a09051e210a0305010506030c12071407030503040209090312040b09031606090b0606160609140712050c031c0305130c230301020a1709 70
    0x1103c0c1c4000a40c0184128007800c89402c2c40744103a180382402901d41c0000514100716800060000101645102c5840c40f85405540303800e481d0303900b008000b0171000d01d80100c0409a408800305500100004480c80d14208040c5c0d0b00c4d00203006440c04100c0710a88a05020802700031244c1d248081031f54040460b14000380000200001245160000c070021000704001100b44000c6141080446601c0f400300c0c0001c3d814140c0d405802840c201003d0030107440d144200011640c201d10501c00c030ba480c56000b480c0d0b141e0021082c644179000700040d940a458175403c0b400032038002c2c41d0120450302d428070301807030890140d6455100c001c010007600d003049840460109a08148420501032540240029200045181540d05010781404088444184650000540c40d0b142da00e0f44000517000e210640f0b40021203903282244543d2808030440701425254503942c0c0001c0030035011811000109024000c8420805040240350907030040c46681c1005c030b05050355614900780e41c00900c0350720103519821a02c0340e6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 966520656 1250 966519406 966519427
    0x3003030b03012c061e0c0c0a02090f040614070f1824090603020a090e060d240f11090402030403050403060f06141e060f1e03100b0703050a1202 63
    0x42503a4100011203c4100701c1010004013400801c1e44001d00c44941888400c010305403100b4a20018000c041c0700303101207011044c0c514100600f08085502518160ba80d0600d8090390510400441c1c00b00e5130715081c0b9440800755404002900d015540a40701c15903900b1400000303507003020354a804034154900007100010b1034101c042504516010804a035248450303400d4004000b200c0e540c100e00c003070600410102440551041e183c104540c1c0b601c41d4004a5110030001500074030101d000034100044944500854002c68501c0c041e40607038000041040d10429800d072402e581501c00210743c103403c1840b40d0070050409030001d640c00340c072030f03d090791801c1c1d143d5031844221042d031518140783c5a6618001d00401082d040850310726401199000d030701d6aa0200305801d000d540f40c1e4110b00400020548071a802c1449050390200030740c0141c41ca40d49100740811903038a40003100e40600c0d2880308140062401001811a2405d5070181c0c2d80b1490103c0481060b51004171442d07524091907820089164803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 966521906 1250 966520656 966520691
    0x1030c0e10120501170d050f04050d0218090717160902030c1e030403120209091302012109020a051008070c020a0314150a0c020a020d02061b073003030b0301 69
    0xe00f01c40c044100b0303101e07061030301e091521040507561428408104111800008e00106072400c80b01e080311440c2c2190f04500c042140f01c4611100d20f101045031609000008002154003811782e1842c45040100260b0110050740d035800314100407845070000c20701441912855001950300082100d1814035240e0a000c8030b80700603074801d1040084401c08000d01c004c16611040c9469101a90b50f015814692030b000000c071b00c00f401416865001001c0d10200d021a40241e400d4a65000340120510400055058100141504035000c9200d41509000850b041c5000390203510342d021a944d80e0b000c5656500c0003a0b894400a110036640410b038418004002030202c0240c81900b40c444010f0840d5545000c0a401c01e1400507000d020824100010721001990000c0d00f4500d00760111000080c1e181c4600200d0700c18031550049500d550000e18030070307210758000540071048441f0704c414020411014a0300782003c40805d400c01042c5040d0b10003140c00300e0710030340058502040050000820301c0f101d000d80c284 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 966523156 1250 966521906 966521909
    0x105091c0b13050f012c0a08030a1d030c0d2607110606030723010c02040f02091215070804151b11120f0c03070f0b06040b01030c0e10120501 62
    0x10041040c40b060300400c03106100c4114089002c500070701032180c1c007807a8081e10309074403c000d241190342c6101800c4031103000c00c1003031717001500903040c50390b80d09141c1d18150150901100d104d0242c25006510807805800104542d42c801c1d004010380201144141c0446810703681c80d80f2128132183c0302002c200d5040c03441c121103018610030786501c00681c821290311800c0c00c0c0001d0071144a0b070040c1e40100301c050b80030352260780108032112444410640c50b0005940707030301800708080d40161500c400c52001c8080c0764001c0024446c22a644403d500d461006150344c0c0742d0040d14110782c0d20f00c240102d650640920384441c0c12921411400700249180c204860441d014260918980c420421480c0c650540107001e202c409509400a0800810060303c413080b5486501ca41c0d03c900e81d030018070207080020034016642c074554013105040740210903080c00c45514101303640a501c20307894038039540b009600030700c2103400c100755680301c9071001c55041c0200040d07540b00e04c00c20014024143c1c0350a0b0162007520a250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 966524406 1250 966523156 966523171
    0xa0c09200c010b010e0607021e061308060402030c0d0c0513140a060e01090207031d0604031b051507051903032c12040506030a090813032f0105091c0b 66
    0x25030301e52400d00062050200100c5c1c0b60050608001540c09a1128102c076041020300c00c01003000403004102246446c03160400803000301000c2480801c0e036090109142c7d000e00d008408403543c01546c50304110b003880071484014a4240010760822032401c04842151184007410381c0001d1148140001d441d888074116103c00c84642e40b004140441c08070001d41a000d0705604c8021810401c1c640d0780540445112031103080007404400f6000036035a00c8a0868010315400144940c18120000c5400840050f6004080c400d00300a42c103290b04040b881c040d2030102d60090001c1c080001403030b403110034081500d28290101510b5014200300140400750640c0c1e011b80c0d14200e20800a000c40b595410001e20340b800d9055030301c007044208105c0d07940d1401c0da50012840c1900103030030701041c0342c1180d1500c60580d04400c2181180e600105000401c070461211103105007180c20000d1086155100d80352410109501192050100401030b080c00c1c9008580702860748a009422103064481d03001d8600300700d0b00078 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 966525656 1250 966524406 966524411
    0x90203190f05010501080c0120071221020316061509020f040504110c0606090a0e150106030e0105010e0a0b06090406091b02010903090528061d030a0c09200c01 70
    0x10781040024803d9900400c604d002a00030311041c41d0009141003a144c40d600b42102c090900b40d8900b201c1400142c005100301902e002141209181c00c0f64803a030121410151018503036100c04032240080111282d1070303101012a003031041d80d07030f84110003071140070010140942c1d00100461388003818401084000000c4640940b42d516090400050780c0141c3d1641072031070703c00d21141031940000107003e030300000101c900300785035541c1003100790003400090350131042403240c84080c02070b241c40344204505a6a01c1c0d94180040350b0450b0490342030324000c3c811050b00c180d0f40000200b045003150b02c1444501c50082000340341040c1c40f000641501c0c410f40281c0112075460b00c0d440c40369011071040c4101c0c910680003e02c11000c094030041c00007101c40c40b03403d01515101c0c0c80b4100c40e04044042e4400944959031184145803208001410302c0e15481c1d8215541c1c0103564045070515002540c40c14156000a171002c4890a1011240c00b4006842411403644000114030551079040c201800b04e050b8400d000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 966526906 1250 966525656 966525683
    0x14070f020a32100629031e071e081b03130602030f010603150305030313031e02100e010e0304210f03120b0103050103020d30020106140604081009020319 67
    0x80c40300301c1d121944038000140000d040c010b0410040d2400908030b0307009601ca55200e5841100749501c260001f00c2d4143e54201c001c0070843d000360404100003607140c03400c1010011001145094038120825107040301300b65100340250400a100d400115805840018000c030002c8565480d50700781e170010782d203c0ea8132014000040c44441e9045c4202040202a40c080c80384851a68480c66100e00c03000e440310030102c04412154041c98025059181e21150708805500400b101c040003e4407103e142c92039030840740c20500c00c81c0c40144140140035180701c0c008091854180b0b4610410003c140c0729160901000c0c0d00603540380401d02099121903598000c1c3c882100b01c04202200e50110b9110482580c1890b143c100140050b8458480101c541c0c1d40c0301d0604001e1540400b00d01001604403200404038100e06080d4020081c0d041d04542c08803640c2c403d4038891003855000b003201c18019401140c6981c0e0028941c0310381c0007000d41201800038006002c1e6844c00003501c5030b00c01e1040c0d88900035902c1440a407a03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 966528156 1250 966526906 966526933
    0x3030506090903090a030308060f060703020604171e090307080304081b031b040f090506070c021f0c02150f040b0405131103271014070f020a32 63
    0x21555880ba4425002d185000242000180e1303003410380c017020b020050f01c500001e083c3e1312107004100713800304024115900c80f0320504e002940e540e011981103e03884902d01c0403c0301d0070b44010594a5400b0a009042c6128000289a141681006050543c10300c030300540003d040200b813000b0405401d005001d0b204907420032031a1150034100e040440d0003070307104841044c40c803181d00b05d00e02280740c4112000b00341c241300d00d03444a010b4900740340c0181035030060005009950760083c01003028244281e0344418407601c038456900c280c006411a8502190814100000600d440c100a10b4640d8083c1e50365410a03451810000740b50308a42c0011320520030000e020700c07040c0342c22007414802405040090100c070ba202c5561903030900020303107548460080040c41800e01c41c403200c000c50003841ca107011034420200c0a84030002070601c03100c01e21b0f105c110400116982e513105421901e1042c103260001c045120b00b0707030380310088140d049070200a45030894540d0040f101c540a0401d0170b20358560004d0141010494 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 966529406 1250 966528156 966528169
    0x30c0318121103030c030a0e0109120f090e0603060c0306030f0109030c0606090c09032621010609030b0610030e15091c120203090304170105091c020c0f03160303030506 74
    0x103142c0142a0b10a0080109652500781141c4d8808240440480c0745221007001901500003c0001001d1558190400c0e035659032060001c405180c0d90354881c0c04c5603648866198008205a943c690950040c20000307060865135801550407000103801c4403202c40021030114212184d0003000c60020740d804045400380501e502480018082610080143e0341a20001030805800c91000400d0900c03030810181d0101b803440100441c0e0f4009070016a80d80d0440749030005a60b04c42c0040d21203200524001040691203603102c07030140c035400740c0d00340855180c403410011300c540c011012800309616100740d0400e404060040c081c9151042d1980038103410183c2c903560500d02e11100003510031000e0b0095400b000d034400c04505200850290050703036038860324002800d502c11340d00a1420100d120821074414401540f209200b081d60724140c40300d02c904145002005550700e04030fa030040c0d21244000d400352400c900d00b01008640141200c80e00320351503040182c408041c1d0b1054010a0382d0f03074104040780c28086c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 966530656 1250 966529406 966529427
    0x31e0c02180105031507030617010204181407110703020a03080304050d11030f1c1e05011e1e0324140601090312020f011d15010510030c031812 63
    0xc1e059031950306220129640320540d4030102441804400840c8003e8040e50046014110340e01103105030140c0c1c1c1e003805020b58054420318844150202070180514014490341c0913100210f0014149502c0700d140403500c81503605100c10340b5010b54100000140d03101d400c0e6400840c0b00302016612403626040c1942003207000300e82c04c07050000c10041c141459901004a940b9805401d454903152070450b00b042c00d20003030b400c0b0413035203140c0703000d0f04556a40700c41620340040703034004001400710380e0700d0b035203120f2480940294071260540982420300c00841c0510914a0a00c4110285041295aa2581d15141d80d05c04c000c2c140c001c4010b46400d6025000b40211011918205a1070041d814101c000819400c2c070b83c80041c1244407400708060b00c40344240b110141c02c2130520001c0c007014071224038607400020f1845802449108a80b02640c5d501d901d071114a041318030007040880b02000d00e820980141c0250203141d4105580c1f0b021070a081240c0e00000c16406018103a840701651189030302a0a04820 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 966531906 1250 966530656 966530689
    0x3080403121104091107020a032102030406080c070203010902100305061005190e030a17030114091905090106030b040c1a031012030e031c030c05130e04031e0c02 71
    0x4098200701d640d4008011202200c02200d80018035900420344039000d4006e0540095120210490000522146102180d401240640505030044102d08244d030390b072140e445018003143c5800300107901603408401a0294038005400464903901990018420710b80121900002c02d41c3c8505012107810101d0724244c0402e543c1c01c2241c9042c102d800100e410481c40c0c9404c0040040403611195240c50920226150640c041e0300080034030b48803200c0c0149900240070341482c0141144082006240003c0c0880c014580d000c800c40c2c0040d480c3d10088098440204140070341c0d902d8540c00400140c3e02c0e4816442140a592000c4203241002400c480d00d800548450016103018001d00603000741c5540d00c601140c80e6207540d4031080c1107624003070303e000080c43d200507858000d40003403a338005102c2200d00903810042e501006800c00d4a03106039258001d80d04514400c6031001000c0c44981216030086410074081d0a00c03071640c0b070149011400951142da2010001001c20000c00118109107125000f41c800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 966533156 1250 966531906 966531911
    0x30605070f0e010509180c130605070516060c0605040311030c07050301180b0f0406060302180403030b15180a080102071202014704020310290a08071202070308040312 73
    0x1217110004200d0f561041c0c24280c20190b400108400b648040102d55a201e2040d516500d01640d42401a125422044003601c0c240075014150079215200400d9509070f07400c0752101440050540c40e16401084010003c50a020030800d45410742c0c3d07000c0000d031041c00390300c2d00206402c5040606040c291540205854641101d0b150594000707080d07030014603403207050b0098420b11079403142810b10103030215030302c040d4220002d1080001e068052025292289008e51004e201010109003400740700c2c03002003010003c03108140214100500b500da5040000b410003400b04907210b890f600c180e800c9030b001c200216240010402c00c0265250280980040c0503c01305091040650000d2800d08030f0303500c1e0391040c9202011201d08418260440d11145860318050811501c03490304c000842e081600c24001c001c0181a0060791103607015030040501039084244c0e003840d0801e0110304040c2e5124101a05160603c08400c0743c00245414501c0a440c400d400381e9a441030300c1c10542406455400300b29030b081001030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 966534406 1250 966533156 966533167
    0x8030405011106070c0f111818121c06180501030c0b030106090e072705130504110f060408030c060f071704030e1908071403030c150709030605070f0e0105 68
    0x181c0214005196035005034070851901940d16100d000980c841fa40c4a502c40020000020f40720368480030103200320b8542d4454410000d40ca40c04907940d0030f000700c26000b8a002000055002150700340d0b40c0081d0048440c004c1a955260301c64120780303122580c3d41c040301a566034010001d00c8408019080200003c003026881c42d410540020160300f0103028592841d04104085056188180010044c0040c50307940121040101202d42d0802100d07880780ca44070f614100c1c1d92540b0001ca03481030034065648009104402c01152041c85a60003c440c8403e034803041c240030029858400f80000c0c44200080c0000c0d203914a00000324807003100c006082c00003042581d0429010b11203d08903647d801c190182003041c0b0603400c100009079a1a0310300005294011815000184580006000350684952590490446050405042d030b0303401b038040b03c0300f503545c80044400d09210b12003d034241c0040e400e02c0c0c4600c0d00c5840784c5498041e220f0a031031030800612b0000406881c1075000c2c198843c500c1c000d02c1e00c203103040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 966535656 1250 966534406 966534421
    0x6100308030a1109120109060c05040f0302100e030f0106030209130b2a040902190309020904241814120a03050901240e0a0506090c09040b090108030405011106 70
    0x107000c010008116070796150002c019244064003503c108500081401003480d070480c010768041d00c401c034001c135116070402c8e00c483c5d1300e28060810740e01901c50304012005002d25640070007518580501c001001c1c080c2006003003100e600d0602c0040c00400540d030001c11071901d1441800300c1c0d1a001055002085200c504030b00c0010000c0c890950030086000c400802894140702501c00300d0303e114000b540e504400100003602d000142c0207011007034050061182c0300b2120200a80503514900c0c1c0c003d600c0910317440080d0004c2c0108045050785c00e01901440e4515007284c241404440201c032000017105440c2c000c980c1040383c80c4010f1504540d100010b462004441d00042c20300d8024000900c0c02d05d0740354400150300e00000d504c00807004007c070030201c00350000c075000600f0000c0b06014200c8241000d40000d40c00c0511401a6401036001401c103c64994410081d86100e1b0804503075103610680b10b04402c141c1c1d54441c1440b5000e80003500145a4640c500380006d05034030003a05c140d80154000070200b040c2c2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 966536906 1250 966535656 966535673
    0x1a01170c030a031d01030e0f070f1211010c030c0209040c140f060412020d0b040b0123060307120f090b010501030f1b2601060f0f08060306070e03031b0c0102061003 72
    0x7080c511310452000c24940d4801600a131240701180308845c4200d4800c990150030005000e0121441c0507112040a5203801502460400c80c0384094080c00f010090b442481d441042207005190180c6003081c0c42c10455030020b014010191401da5109400743c0c0d003802810450f83d40c0840c526405c54020380a81d00300340100d0380c140518401c80d013520034090000810b40d180e21076a4007025a20203806192850185071110f4425420300410118039002c82c1c158000b02c40c40b1306050000c840c010710450541d40c44084c2110100d411685182500d602c1e10328030400b4048500446c02401e10404031440150704000004080342c0300328041c1c9001c1824105006241c6401041c044030380d1030b00e071401a1444103401c040f0f02030066102400000c1469010001032451340c050700a000000856075132140d0403042e004e0455004100b03841540d8550400004101c1080c001d1032a0210b441e8060305490401d40c1e074070030040c0c0755560f05031080300c180c004042510041da030501c02c0503404503540584451650558988010703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 966538156 1250 966536906 966536927
    0xc03181514041a0f280e01180303050c07020d081b0703060e07050625151a1311030a0b0a3c0501020d0c1a01170c030a03 53
    0x140c055294046116499580140710a4a140e4040041c1800d042c6448410366089400803052500c0b8100800c094400d4003000601031500340800e00110421740e8460000d40a00f241d513200c8081e507800c10711001500a001d070000030a00f544140f00985143d007405416590000c05003414007000700460401603450340c0349054030540008041d0380b01c1c102c28040c100d0340800c048ac5a102d0b40310350b4a00004010300303504411400d4800100361600d480d610024008980126030070700e0181da4503610700c1c080f0032410001041015024240e4402c8112551500d0b000321000c01c01400300078082c2606807611030800b1071101842c080035150411280c94000944c0c42c0c6800f0150000f140c0759160030304414181d481d000b041016140a07140f42d5098541400e598041c02e0b02c10500400d81c02540071034045072800900913104685044e0050300c0e210aa8803411603031842c8525003103840210886402c14444210400316029202150a4a0032a05114040c0781f41c14030840c0858440d07441110140700081d485405030302c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 966539406 1250 966538156 966538163
    0x1f08010207110603071d03010f05040f050c0d030c02040527030a1803031e27180b0102071a2109101b1101020d14060a060318120203040b030403020c040c0318 69
    0x415011700c0c0f00020340902498541295052b0034881131000340710304441c01c0c0740c41a20030740031107090380d943c1d8083c010500e00b0351030050049042c1e115440054289a08030796401010a1075044805403070783c40760b01100342448048a15039101088220b0415000680c1803071200041d0404411985150303801004a054142d003400c00e60381c030b94005c0c00c0d00ca020b822080203010194414600b02a4400c0410070050520b108006400702080c0b010326001d89588911079103000180d0180c810705083c010b41c403000f51010b00700d00d003041e139081260307860501d01400c98100030f10800003c545d45040c003c030715519286542c3d104001240c034200b07600309000c061039400c204030300c007500f4440e40d07442c010007403070340240210300400130030b5410005c0011a2024003c132945c030481d0101c481c00038107512041c0403003c0790f41c02c3c0da884201c00745a14461000c1048480e5010045d1450720440340b03030544915120301c8581041d2421030141c6e0100400c802145880e00500320780e21294a403c01c0300b181d1840000b18107801200000c2d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 966540656 1250 966539406 966539447
    0x6040b300609060c0a050f22140a060e06091f091e051908030a02010c090b0a051204020a0302120a15110304020d020105090438030d03051f0801020711060307 69
    0x603030b0b16014200b03444a803070105c5140c6403a401040080da12302d28488080c8204a0454000425040c0540c6007180003d00c001c4e024030b0080303040030000d0300e0100c0d58101c0c0079400f00041c0440406582c8004040f0704c4d24002d03422004a0100d18000a8450040c5402184e011202c08407030384000b01e01c4401d0241200c0d400c031130b40c0e10b01d140c100030039030405141078101e048a13000c0007d0b6040d08070303015000551002e02c00e5680c110b52903524410001c9038018280e0500005004201ba100140c41150446400600007494414040c2d5250300150495000e0000900310b0341000b07810f0010300c401c81003e4040c002144034248400140c202039041e032488010002071080c29003000c4070040d6481181511000704004c3c00801100121540ba480c0503051100011003068442440402956125a104201c02d0700a00107000f10020118190301600c0010305183d014401d0f140040c10044604a003807006041c450001650b8140340d0400304a1481aa02c44500511080082c010314607030040c01c41e0010101040788 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 966541906 1250 966540656 966540667
    0x7052b1106131d1501020703020103090c080609100c050304031416050607270803091c02150319110316030f050903120906040209060906040b300609060c 67
    0x26030728000c0c1d0b004403054141c41000816070641c01050f590058441d4209010550303580b400d0780051098040c8440d0041e08880c0d0f0400042d40660468030b0380e1807041520081064444407404e1901001f00e074a100150303c24036106441d100c03030b071280d08590080c624100d45076150903140500b0b480036940c01c03078480c40c1001803081c81444500d00030702e41d02ca80c8881503910b542801100140b0500752a9440c03400402801e088028800d46070922504560404c1c6c0618180340c100410040001c81074a15081032170450f03080b000c0140e5820f29068034544403c0b0040e600c030304240048500007400e0180300c8000600d00b0410720500c1c032072002a603038051400c03002614003010305d003403c0300900815a03803070f00707014204024015880b1020021380380c5001304009010721a43c41210050780d030042510003a4001140c5802f041c102c0c2004031300075600803005800450032081d42000b10304200c01c1d110140440a80100c2038003860703a0300e04c50000740d1076807820041c9100e00f070038004107440c0c1202618000b00000b00051 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 966543156 1250 966541906 966541909
    0xc09031e011b0320070c050409030507080f12130c0b160c080309090f100329180105060307051318020604060906141612020102160507052b11 62
    0xa541094a0300049480b803034011500903015250026100441c2042c0a000e001c003540c8003000d580d4280c0d0025440c40740186088240002002440d4041e0308004c8100004004105c4540040c5280e0900248441ea19a10a544d0405040003e003941c011b020821b0100340214010200309401d07142c08034038403541c900c903544503001c00d6425180700910584283c4c0e07001802d0000400038100d144d0041c0d900c685a07556140207802c1c070200440e117079041590b0704281400880c01d000010006081507042c51b2280301c1441c0090204180c1c116207400b4012a0b107800c40d038481c0300a00559402900036801041c0301414180080c014410b400321410100d030b80d81155150003601d4100d29030140f90042d1500350341e40e8603031000130b20280a0b402440e001ca10410401c00c41c404481003240c51450142d10001c404025950f40c099040c203c10800b0f000f199000c0c1b100f00d20001c5c0e090000b1465038130031401494564601800d0040521190320004c210030388402100801034500307501201c150780e1050324115600040030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 966544406 1250 966543156 966543161
    0x6050a1805040e0a170403020306012c0a050a200a1202040509040b0703050907180c0e0310020904060504061a070302071d04030e150d0e19030e090c09031e01 69
    0xd2050341d11504041c80b00c140e0903c04107809103c207000b8480840028044495003102d803050707110007501580440010001004030300c405050b0f0104540c1c0c001c00520b0405465160341c1e07825030f4400095a61503061001540e0140308400d00006640d207004039081a00380d000015000d14015907081c813041a21401c100c410f1030b070448000d004000e151040741d0400b03040140c25040100c80f03150200b807428020075008100024110119607222a0a0018040f007000c48406440f450303e860080c000c5c400c403001d03020340d0b0501075491456a0320900684a186d0002080301307484240e480f482c041c80c0343c04014041c400b0100d01809000310303611b40081e075507025031400301e2410360300703a00521204003080034401051420000140c041c074002c0d503901600d00c44480c01c02c00c14000304040a07081c0e00b4100481d4010b00b41c5500510b0342d183c4400165504802400c0c448e803101a01c004c030032000103c0c0b070f80d402c0070540351030401075801c10005000d4906200310140800e032f5500740341f0144d21010340440e02d900b80c040c0f400d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 966545656 1250 966544406 966544409
    0xb240d1e2c1b061905040e13050304050d050c04110d110309070501051e0a052a06151c0803090105090a08070204021606020d0b0109080109051009050c060a12051006050a18 75
    0x72031a613003400304042002001a0810300800300c0031101d030800305045100310717900d0200840e00078015600e49450a02082248120304100700c82034000c500b13a0000603500c0c1d2083c03101640c505011303a45c3d1a41c107021440c04407601903164070390641003071051144504000134190f055560a0a01e00d0f50b41c00080b900d20800c1c2ca01e0b40c8800210800010040301499110340980001b5030120003985001500c0001b00300c82d0b90361001351080c1503100c600011031b075a24501c006508110701400c01c070300201001c108000f5120750031609072012030000090102480e0b0901c074003540080c518000c2d00304a100c039a1080c81c680710b9544040c0c032603a00400d0401080d10821280400c80c1e50060086644801e5460700b0400b03041007000842c04600c10040004d05e80006020b500e0206038000b000d0500d8994601c6914000d19800300c00f92001d125851090046440300303802081c241c000e50700d1b00120300502641403c10340e140204074038040303881d029040200913080800e03242c985240d810144082100340c2000000c00314103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 966546762 1106 966545656 966545677
    0xb070312060b0d0f0204120b06100801080604080a140c0a060b150f0304050a020d0f0c05031c211e0b240d1e2c1b06 51
    0xb50360040c005924100c0c001411b041e00c60f09038000f02041c100d4200c3e08441c8280a000451408030640c0e28030503110f00d800c10140d1304094506441317010290004101343c00204980999070700480204000b4908800100d4803030241986060340d0341520348040c1c80b011720b171044900721707800c0c42070b100b009101c10340541502e04100071140c0240c0341e00041c82540c0701e0180081030001a074401040d055401d0185050b051020702d2307802e28584040040c2c0c031492199022610214030009980c0300400740b401e141c1008004641301488005503c25102002604907160001401090005441006142c41c502c402002000380605c00e01010208034012100400c002103140c0300e40ba00d4080080c401e0900805010643c040365410007000c4448851100745d801d0386401540344e4201c0c17281c4210840e03043c4c0080081ea0b01c8118000d0300d40342d44030515035203100c04405152038120784a1304112a541440b = true := by decide +kernel

theorem cover : BRFrame.Cov 966366906 966546762 := by
  have h0 := BRFrame.cov_init 966366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 966366906 ≤ n) (h2 : n < 966546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
