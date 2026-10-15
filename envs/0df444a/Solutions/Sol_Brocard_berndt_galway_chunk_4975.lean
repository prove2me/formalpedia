-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4975
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:20:19.668443+00:00
-- url     : https://prove2.me/submissions/d7867c7d-3677-4bb6-8acf-cc8890f7a178

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 894604316 ≤ n < 894784172 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 894605566 1250 894604316 894604327
    0x21905010509060c0118120806092e030f08071202060105010519020a1401050a06061d0904020112090c1404230c040806090c0906090709030f0629010f050a02070b 71
    0x4007544038496003264080000c80ba0803140c0381003804501d03440c000100041c031550100e4271615000002e5406035214003040c1c40c03480b411b0043d00c020100685030801243c01d0710307200000032030f00c28018815503030701c50705880e9521510380c0b503c50002d02c86107040790110340c409001849166040000c44003090300c5d442d604c2440c0b40d4066801ca2070600300b501c0040015041c40711000510105401c540d0294450702024440a5103c0c0d00407542e0340740303c400da1220044c0004a040181c20301854081c0c20900600d4802081c907401d4407500c050711001001245c014030852001c00440b04a40c0510041020844080c0003111642d0740105040200b151004801030100010580c0c49a00c001158020150304094422604d030610341030340c441d00c0c00d614050145c0034010002c1c1040c90301d292075900c036100644458144034159191b9244441c40d40c801290000c0d80c1d205050703840c40e02c502600309800202d202d40c0001080c0b000005201003422400ca50901000303001d14024260085071010540d000304045540b0390 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 894606816 1250 894605566 894605587
    0x4020328030c02040912020a0506011517070201110301120c0501141918080102041e03030c0303021806030103260a0c110a030605090604121407150b130902190501050906 74
    0x5e102802006140c04032101741064259004a440741565008005a40c030a07070f680d26030080e07546032240ea00000201840114040c1200120805400c0809031000040c1641052500700c0140d0080e0440089444840c01c0b117000c000941000c1406084203107070100c2d540507240b4004405008001d5035280d450000b500c3d1841c3c007486004007001c044100701361900c420b0f588a0ba494000d500074001d11a9052000c0e840404200c14081000c1c1280d9040c7c1d15900001c0300c0342c8045009412515448881c686034005c02c14503541c0342c0c409103020358010a66140c824418140400100404102a101c001c0f01406001c02c03058111414145a94101104040404103900040c100c00306a80006040a00c3e100900c02c00c0100021024411071003010b02d02c1c0001c0e0540800c0e84c000b00c200c004510318039800c010800002c3c610f440d08240c0358100c3c10010503940e890400180c0d017458103120030552159190355030001d5240c035000000001104011085d5403a003840c0c0000e29504c144100c0c240100400520300840 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 894608066 1250 894606816 894606821
    0x18090f15090b090a030f110106030203151603150b07030201240f0806090705130f0504060b180f01050907110715120c09030201030c020c0a0b0304020328030c0204 71
    0x6a100c66590301900050200c0001030149540956442d40a4000903040b8800050010710240e016120340000c90040402102c104440c004855044d54071a840000141c60401c15040a4089030f91001c80d1490415031403c81d8000070303200c600401d0b0910080c1555500c107440c14506544907003009035a5040c4605090340902200d8410703800c441c010400c8038218004440254050310190918030070f0309a07403032800c0c40d51060241c3e80011a90010941000140340c12030781a100281d00c0781011480600000c8040c04852084801ba038500380c64031000285450950049070416901c02c1005e5184c0c00c101608040f030300414051140030b084d10f14082140300d0701030703180c0e01d10402d01c05040320f0105496000c48140c1c44071215030341d4003007010700c81440700d5148180265032310a02d80f55a400c64691850b001107018125500ba42401d5005103c1c004c0c0c800c0d01c42040400c050308071101019602d003418030600d4a48502c00c3c1000d4031000f0000f45140c00c115601d10326644450301490040450381050000500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 894609316 1250 894608066 894608093
    0xc09010c15110f0409180b221a01050f2407140a06090201030b06090d03141b030301080c0d03050d09080d020d0e010b120309060706020c030f120a061809 67
    0x182c81c40c0860b840c800107028600900c1501c4444206218803c0da83d01000d19003600381c2c900a2110400000060095001d1034603500103094510400e000301b500d6451b45295044240310300c0004490110041c040c07414500c0c2640c03000c6c4400e41d04289550403c201401c078100008038050301c1514002604014013942402c0c000190203003400340c070300e4140c582ca400d400030811031004a010a007822010180b503d400070581d20a01c0001e8404035580506650454a142d0807010103c48100c040c0b06c0541e00f403103040360001b68400c1c4003008550341c1d41490000c40c5810f907a030035098404c524406092000070341c8a800da4200014244022034040e00900e00520103025581400d040d007440400c1d8512481181c0d0412000100c00c24000c1012441c5c0106108410f81800c80c0c102c4143e004200c03e81c15420f21100920050b40105001410a4a182d14150035940a100f8200c02210042441040900300c1650160000c0d80d10384200b1185251009a44807512001c8100c01d005e9912081842800480780e10b508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 894610566 1250 894609316 894609341
    0x250503060607170c060709030b010b07051623030706050f0a1b030c02090f0907061b0605040305030f10050a05060c151f060924140304050d03050c09010c15 68
    0x410403079030b42c6083d20540c219040088851007103001003240903000c4c1541400ba00c2d04000003414580c03c10490200541c41441c04030740c0b600c64401000300408034003000c0383c003902c10060001911108140c04801a204c07880c00c06100340c1003504100987e50700311007250410aa400940342d240d4070000c0040d900303003200c00160000c40910040f0441019401040c0b21150f034404c03039102c2c1e116143c92130b81c09060001183d50480c142c0c00114107003e118054141c1e030409410824006410840d550b542c007060355015142200883e0b0040140309070203072041001540292130081c41500310b0b24040009140711464400c45000b140d0005880c0b420b80814030003070350f400320f070710115101c9802c10392450200e80001e02c82c1c50b2440301d040080450b20910075614042140c005c40c1e83e0540800380d556101580311000d420040c00d10051841030410841683c000d54803c078061030103042800b04961020301541d10082c100c9118150420000354203070f07048207228409642103042e2501c0c1517550b02c4000010b00f007003051072 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 894611816 1250 894610566 894610583
    0x10b1804140f011409010c0815040e032a03120402060d0e010c0c050f0a151d060c031609080a200a030606143703120e09250503060607 59
    0x1400840c150002c59250b40030488480842d545c01c003e280c01c075107106560800040340580816901c0c04003511f2142d5201c4020b200244108655070182d1941e4058060a0b08130000000c402c2c0c01403080908044e4501382d5440954a443c40000c40505607000044c03009218140c04a22089008459403140800d8480400204a4901c80790006003400e0040c50045030248650244044c84040205000c140720fa44585003c0c80d00ba2403410041c0a00402c40001d0007030450806050a920020841c00e4041c407005030751260740e0f081c40140009855180644502800200c26080141000001d50614400d80000c1400210320200c1d079038040740c510311424254030101d102d9002c07040c020300340e00c0302c801c54412005051190b0300c100148030382d00000341e00f201b0014481c886002c11404800b9207050395101028002d0001c01e46a42c2e0701444c080b10b610403035000602140304a22242031040f00340e5040702021101c001c3e105000d002c0312440c0888801104104880400810215122041940c00869220611 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 894613066 1250 894611816 894611833
    0x50609010b070f0210030e0c04201c05010f030c1e0b160501150815070807050d1e0203041109060f0d0201090512030304050610051309031b050c01020f010b180414 71
    0x8002d0f08010300c4940c00c4d0301810089020510b030a100705003a0f80c040c80881403458074249108481a00000c100741170902c00030072f010842c00381c00c0c4621800707000340c05040920f56042d400c1501401d58503401440d00702c85414031016a6800e1780c1e4004e000c0b12103e0403500c0e514a601c1c90303c1c551b41401102d00405940c01d00c0c1071708241202d6900241d060300c0742c2e007003152003004902040d000d02c1d5a00303031038003c08030302650301003181c2c14071800040028800000010480c0c419019003a60000185c4c0c1403007842943c0401400104440142e0002c3c15500c22203c0b10b80c6414284c00080d11003042c2100c55101d000d42481140071039009108440003002c004104500c807d1230008515125801110b08540c540039620014500e108000710380707800e840000d40020140d40e00f40c0d584d14010080c2c54000e80512002c88050340005481c0c0e25203102091250028080b040e900d0380019150100305144541c0703903410042c40d94043c0d2103050362009900c205a1180c0301940701c504001c0c41c05150841500224000c2e102d0703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 894614316 1250 894613066 894613099
    0x31d010509101a010e0105070b07021c08041208060d210f0906080423060a090219231f0512070f05030a0f0608031209060a050609010b070f02 62
    0x80944581500d006456512242c070b02d0401c00c651601c0704603000060011036000d03165100300a050010710f81818290b1400c00141c854500b111000c952030001139008858107000034000062030300b6000c405042040d480c5c146661381001c200d448159040800c4000f10000b20240c0e21a42c07070380c190f6508014003400c0880181000c0c0a805110251800440c03140009050000e1081c1d1000c011910282e4414005450343d90301c5980216001c090712850080c0e43c04000c58111013840514014401c0850000305da0040e0b1040c04600701d40340c910b507100060443c1c1c04000c80600468100102141e5100074a46020204000b800607100c0d50b4074194494261001038116503080802840c40d900b05032401d43c0c05644d008400c40b02040c41f0800e1500199050001c905001c8858010a40b2880c03404400700781140c40d08080b500c3c50308210703030103200c6800510500601c8001030021170341049252500740320b981307010000f00d0700b8900d042c0701e6611075140000d03a8105001100500c0640f40d60f008200304040e201461 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 894615566 1250 894614316 894614321
    0x1121e15120b0c070203030403060e2104381201140301020a0519020f03161b05030316030215010906080606030a0b13030e0a0609080f03180d0201031d01 67
    0x24080d400344045030a02144551294126005240d44000c280300301d03070380e01012440d158100407012a0584410301001c80010241c2c055400c0c00e50b80b150050004c8050070403c403240200c800e2070554540c104000a210605449a41c1021265990301d030603c00000342c001c40030342001e240403191500c800480c10040c100780e001c00710340c125211010b10380c0000440741c042500b00e01ca2403d41102180301007198503a03390709184190100382c80c600550722020181c2c1ca81c82d0455100d2080e82d100081e00b00c003170604200d500000c0107800c03500d880c00403400b2410800420b81d2480b99640041100c0100b02c0a041010320821004079900d2130003905840c2565118040000340140d802000018018003002900c0307070a00041c81400250450b05150140d100d008490500c45101032007501040050aa981c1060703c0c1d0310080c0c0000c001c0780e03403802d150f0703031500042906114103a50341c40c1c0d05030030401c00c1c0f141d0340001042031016058122503100c00051903200583c020a03d103019400500c0650b44201005a01075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 894616816 1250 894615566 894615581
    0x501300e0f06010609121509051014040c03170c0d0504090b06130e070c0209040b0f010b0a020a06021324030507210903031e1a1e01121e 60
    0x400c0741c1d510001245a151220000d001e46800140c69680400003c41ca040440102c2400791740c00c2c1440080c03141420301550182c181c02e40d810341c80303601c108400d09528821003045100c000b20452885c01c0650b1442d14010280c0f00c09801c61404840c2c407540c0c0b65811080b141d007601c0c07080440e013070030a0051000d04960402d104004075a440c1c02850481e40c10071108580c0703034403290320400344418140141d4040d00c03880074041c44204440d040340e040040c2c64244000d0700030f0740a400301d0b86a0785896040440c4902c0140c014140340d1200f484000007143d000038411903243c1d0b00500240e100c1c0800344103c241c0302c507542c2c010303514400a250700a81c0d41c8024440681c1c007020035a014402503592140545021000c1520022035654103050000c41c01c46039130084917140d11030f24000c44c15800003200800c0b0444e8500600050303d6507806118629401c1c0218401c2218054a45400e504091405645005004044541400000d184081e807a400a40c03008021080c0b410200c5e91a034000303404c010081014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 894618066 1250 894616816 894616841
    0xc1507170105061e0427060f03031b02030c0a09020d0b010f021e0705040e07062303041b0e10050a0815010308070c12030503091c0801050130 62
    0x208042181030a41144250580da0003401e06498800c41c218000e140c403601c81c3c00705044030024480030a01c0c654800312109170038503041c04c1c0180301c902c4550440440c0ea081e408481d0350042510b08000003500155103081c13114011408440c44001c40c00444d0500388414000b55007e02c1c40d0101140b1034200ba40900407000c0d5248013080f00824050040d10070000c68918100580d004149552040c402d00b440e0800903e811019a001e640d501c0c3c012400f03841424018007000e4221078000c0c410340c0c1d4402c00108801c5080d522460402035010003c070402d1002801c040d00700651040c1e00c1a0f4940c5038222a00180401c110581041c50315400b500100c05036406600e124500082c80020000c03c0062035605000e0148203203172081e46540d80e00701c2d03164003200c2d044464035084000028400c0f0b02030105140c560007611030a42e40e18040030800d0501164003d0517a1602a50000c0b25980e82d101981905640b030030f080540901c159400c104900b2041d01c0303154100705a01c06510844440380340c11a84040c0380f03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 894619316 1250 894618066 894618077
    0x1106030c0c1902030601270e0c121b0d030203070f0804050406050105030c0417070807080106030b0609090a030f020a021315050306160f090803031e060d0507090b01050c1507 76
    0xd102c241e0104002c42c1d0302000c1d5056210500502085c890a40c07400040c041c0503441c142c00c025464007c50658603000700c507009a0700300031308803c01c904202e80c507030040c1d04140000d03241c8902520801c6a407482c0201c881c5000322070403104101058002c100320b803903035038001c05028404450b034907080260780d005004044c001c600b07001000401b54051015640154081d5031414202030501d40c0b0341c91a030040c8960707826a842950b000241e40441403004501400c611400402d096046040000c3d07100405092240500b414200b0404290004144611503d905207401c060201180034106d25180451001950003850811902094140351f40070004880c00049843c0845581c1d03400c05d81c40301c5003160b4809002c0c01d440400c02c0454450b9011103000ba00d00c1c103000b41c22070b4817916503e24642045840c080303c4a003940d80003004243d1507031026400482203407007584200c002c0d0349581c0c4039043ca110306003100c0c1d15440100d5191b8080c40545401c804080111180f1800c107180980c014801980c8500204c0c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 894620566 1250 894619316 894619333
    0x190606090209130f110307080106080c27010306050a090b0420040e040201120f0c1206050105090904081b0a0615061407020d08160c0902041a071106030c0c 68
    0x2080c0295421024001e00c54000b0440f4800d08401619900c84001040d6603511201c0401a82c00c1005e1402061103643e42e080c02d42c1800303005400124054491700c00b00da1f042c0b08180c1001c0c40c280403480491494491000c41c0211240140e0203002c4036003060741e01800345040401c801210368850200407108940900100e40c03500301d441c2d891a80c00e405200d09030401c00090110701c0c511042c1940091062502d20301920620860008076681080c0e1340183c09d484240c03106801d07503c030700d620303040d004040810004149448006440c41c03103400406405030014200040a1060b404150f0324400071044d0082c07803d000310b000c25901c440000c50102e4085281610400c01c0045070000300c81540c3d074503140c200c03200c51768002c02c06080d0009007040780d01410541c04000007030082405040c00e041c04d243e60000d00030301c034600254442d8054000c0d1070300d584148030800c6a140441408620030118440079543c80519050090085140728005c0d500488004107204940c0050b0303000700054124041940c0b10038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 894621816 1250 894620566 894620579
    0x615050d1503110d0305070203160501230316030605040f020406180e06040513050703051c03140c030603070b0f180d020f010e190b091021020f0705190606 68
    0x100742400090544001e52003002081e08042d40c0c00c264240c040d086c003c2c1030580660000b840c08100d1914680565103900c000c00c206d58100c0000c0810030368010f80c0c1848850604115030481c00010300c48518140003020350a0380e01d0107940008058540544140484003404202034083e510522586c00080d0103501590945944681010282c41d007889960a07161a2602013201500010302103d0500c0b444810f89000520100301400041d032140003d40010641c4503196101d9030891504641072609100340601131644000d4195407100406000c182c8a4a03901e0110386440c3c59038000b000540d4000075a0040305e55408003a2036000c4203090301d042440152818411951000e030002900b0000d0406607840c20344c081c144201c0c4885018050702d407002205000030108995903070100c22044000164840d0030b0a189100c250264500c0c10b00456a0510f1011000b11030140c0310140c6c1080da000c5101001410030b041118400d580100480c1c0ba004c04035481300740e0403480c000302101e09a10707240000444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 894623066 1250 894621816 894621851
    0x6030d2a1a011e030f061e060303110c0303071709150d050a09080d0c12060609030b0a0203091f1535031803100219030f061a0a030615050d 61
    0x2003c1034034901c1e051462643d9200308000b42080c100310b5250340c5400f85840b041c0d0f02150145400e405031080803400307a156042c00f510f210f145a00342c580c260040307078048491307840002c200d8110550014145911202210710340c4110b000c0c0d1503806610039100c00030a034280020303030041c1052000e03580041040307445070800a0100c03414108024111001441082c100c0d07206980800902c0c622414404c405050b501c0c2c0785000c661040c0c022001080109200b4401e01c01e91081d0950700603a069002c6155082548aa0b5030720414070300404528090b01d00b42008401c0d1a4206004101003e2442064261114a06031196818418a0b094000351810a0001d90a24482c041070341d0085409035180400f0300721000c241b400343c1900d4a4140c03050f0081c1c12911595403005003c20a041c80b0389070300c6154011401400d40f0380d60105824070074100704040c081d0610356035100e10140f002e0302140c1d542d03000794a0280c001e0841c0c0d51110a1250400303136040c0c14690040300400307800a20b850100309480c85422020700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 894624316 1250 894623066 894623099
    0x1002030c04031e0c030615031202031c050c030f0903090303072a140f040b0d113303070c0501061412070b0a18030b01031a0f06030d2a1a01 61
    0xa036260004c01000414030707070b07840101610390482c06400c402c2d4883c5c030b070742e442e4400302e241481c01a880001c2144060106540c01d44560100d0541402542040c180001c043d010241840c51080101000706403018010070803200203a4020702525180e0341903003005c031401210400035090809000703810f84901400c1101080c1a5251940c00d0311208007004140300341900d13006d144070b80081d036601040b5400e6648a0244080500c599103011008000038107100702c0301d110803042c0c15440300e51030403000c0000104070000640c1284a18440e1295120302c0308032640086080060255440c0010128050550b814103042c0ca040960301000d00341801044560b8460b910300c40d000904400340803181c6030074031444140700a0780d84c80310749900050f240d48402d61440340aa000b1107003022038840e910203608085004a40c4403020007440c021502e015804203880c1c840e81c541c1c072030070403144200305a070494991040407103250004050314050005442e115982d6082207081c4402c0c8154030000103000f0546480808 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 894625566 1250 894624316 894624323
    0x4030c0806071d12031909212d030f1d01082a0c0d0e0a080c09090708070303032a230d0504050d030b030d201002030c04031e 55
    0x103034018001405850500407107181c0e84d400080484103040f028020000f920a0542c03200003c3d48038050828050903518803548100400c7c83e5081c11044008550712030322400c40c7d0016000d90241307084400100300c2181207071201c0c07841d426941c0d02105042d031202070180340500b40e8031800300a1005000450025904126440c0001d0b000c00009059400391441a51b00e0340c1c0e5842c03050040d1840401c150120342150b4a080013642c8038085664015500103403140c10340d1400d82d50902d603241064080c58a585484414900400b21040403c3c144042000b039400181007600030754081940720711b0001c01030b00d80c080c00e020101d01c4502000003112540900d02e0100b40a82c0c54105180b00c1e00540303400d400703c0d192568149803a0a12807102d00040f203000e801c1c400c03031144000d0300040c0342c2145d0290490300c0300c0d40524020703800f4103215805a80c12050141540c0c1041020240c1d8210600400c5e28100308400904171150000c4140804800603a015005072489a02030401d000c082860188682881500c0913 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 894626816 1250 894625566 894625577
    0xf0812060f030309010c020310060e040312060e0c0c0a080309010c11060106050316020106090c0504091a060d0f0603050d03230c0d180f05061503061506090607060501090204030c080607 81
    0xf400300b5802006c1c0c00c0301152018007035894081400400e2001c603180d070f6010b40c41c095004000c20007050303405a01e4030b18141c1c004804000c0941001944070007454018580300081c00e00280440300ca000412158986c158440c40e4a662440c00d081401d01038504003503507a01148581c1644480b4550214485060760320603540d550441d0784d2417140e203000c03122000d50078065568845012500314100d00a81031403a0f200e40301e0a13510382c42d00326020202c80000c403615000300c8007207820001983c0c44404552150343c42d01008900c4284a43c540310040c1007940c001040c9214100300c40024a405800001d0b1001d482c0c56000489486810310703904503e01124a16410003003001484007284840c0d2004a02d0440081d80d01d501101d00e5580881d00e16000c0806c1e10740742e200108100c000d800003ca10f0498605c00c0d0054540c50415640c1ca01c050a01c0b051024420400480c0340240c5d5100c1c0810b40380340c20f80145c018803403540d5442c440f1009500500080d07821558502d0007094040c07002446a014160944c1c44 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 894628066 1250 894626816 894626827
    0x42408070302090c1e030406020301151716021e1c0f08130809210601080f03030112060b060301030f0209010b030408090907120c05180307050a06050d06030f0812060f0303 75
    0x141131554000701003c6102440f201041c409282d10202031071045110b4000180d03207506003400009154241c4541f501007048212190101a454200c46a0004038040450031034040046050781006038120450001c4007248941400312080000c10880140e4200792207c200c1d904200d045410114030705405000c90401c4000c10400a10000e5020000d40200c101e0b0341022031500c00185182d002c0403480071131000035100c0c0d410360703a810300545004001c00802440300c5040d03882000c0c0c9a00052140411a80285581c0400e20046412420708100020415079980d83c407841e24110b038001d01801640214108400400c980c83c00c60101c0e130140340c2028100e4204000c21080184661008141f241001070141d0740d209214640e0040c0041004142c5034a901d915500014960580041c3c1c0d0061103035104c410100709607107660704004192412460259030b507038005590b20028180c9030340b0050103410b00701403410074841281c0c00b030014020160701040c001e445410410440c491900e00716070349a0003c020 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 894629316 1250 894628066 894628081
    0x5010f06050c070e04020114030708060a2312070503120309160e190b0603010f03110a1208030403090f090905060604091509030e0d1113050903070b06060904240807030209 75
    0x1380698403504c1490042d01c0b01820a8912040b50001d580701ca0114500c5d1040c8480c6250982145001d0146801f08400c1d90606038140008500440303110350040158070810a580ca8091141d00041d1201408461034292100750740b45c40c030b6008a4285c0228080e10300d00741141541d450f107103800c5a0610342901c1c0716071280d12a00707403914400074450080542d030341b00310901034031408051802428122140a51945142032258444004403c010b201d0684501c0510000d0045842140299000b0407029120390f034a2406490020881e080907a1a0b00581c00000f1035031a0f070b0700854000da100c1c40585101f034650b20144410b8400c4d042000300000250450206420103d40c01108200d010345003000c00c0015003404103640518041c415144225840007140d124109800042101140101d041046141c040c140039205d0085c0280103000d1504180480d810f9030f02c00043c1c0d0f0700c40f68028810445504a09914410303c80325101c1011400c502c50000100f4000200d5071400322600500182e080d50354616 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 894630566 1250 894629316 894629339
    0xd081501050d0207060608070501090e0c03130f05010204080102071a0402010c02040c090e13121706090c0408030a02070833060402040f0b1e0306060d200a0305010f06050c07 76
    0x5400c00e0103d60038040c050100f015405020000e000c0c0802030920103040c83c000404420068010842564021007800f0070048000c0c1140d50000800c505040d002807a441d141d00c0e1841100c5010300258000714000c2100d81c4194002c0040500c10060210013031014881e50998105c100c4003e40850040c013907000c05814a6040000366900c1c42c6021407603251181c1c2515040213041d9280c1c11604d070f00302000c004021220b10038202c0001907007406044560301402e500340d1004020117090045180f200400c15030421a001e84001d41124025240c8600094000950f5130380c1c2c5108601042c410100140c6954010513440c2c0c100507200142c0a4030274084440784014140c01404841d0800c0d400c03c8002292440500d2a030090245403010b02d584c0c50500380980c000b000207012025031741d501001030280310307a10403045038281411442c01007100340000d41009076045a00003000381c2c6160010300700216942c594030503070507075000e110459005178070f40d01c040700d05000b140310400e9940c3c400d103014401c607880319 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 894631816 1250 894630566 894630577
    0x40311072711182b02031b1f0912140d140a111e0304090c030c0c150b0910090f1506110f0a03080f18060c090a05060415020d08150105 59
    0xe8144d012411207415184078010002c552415040c094a009a0842c0f40603c001601d80c0c541802c208130001041000451440e02c0000180891042e105810003880c041c01d110310040c02180c00050300a0054182502101d10350850f0b000d01c0d005041c09101440d0054014145501e041001d00d8105004590309540300c0790706840e004d50502c81e422119500107016803002c601d01740c0326800b45445a151108000c140c2e1000040d0350b080c10708103074150680c01c0c0e00031a04c2c2c0c4050381000c200b00317949100384420801400385600381a0050b034182c04000041c0304041b004011031710000700801818504180d02d000f12440311009044c00d620440007007100e203100b820011542c01c4d14100380c50211511103001803400150850450101c0d02d6441040180810b0500440c0c4c444c01c2c51800c035440404601042d80c443c84001c1041070305400c0030400c9059a125130400401030100038040c5c80c3e490780c44e020012468030506210200500c11720080d2030b982c40c480c440d903d00900c0500c10040c82d1100c10001503541da0000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 894633066 1250 894631816 894631819
    0x181503190209280e1509070e09010920160f02060f0706090303051f03031110020c0a022d09072115090c02120304031107271118 56
    0x288a065566603d0981001e005482604500e1032000003150300c1d0110b9401d5030000702e07005800c00070040803034180c0303805017010307541103071800815901c200f015038035601c43d091034641040445001280e080b603154424031029001200c84017070b020a20310310510034070688000f5203007842c1400e01200000c40c80c9003e840c0f0a403004049038113044210a2f400131070b82085400340c803115142c01130f4600f07142c1c140c45070581000c260721007108010380d524070714229001c403880024108107410102002121b41840118001d0300c0c040020b56030340225607002540c1e8801582c080c0d105503011001c5240d0307500301101c0b42c4045000804208140500b910030002c603200300504440520000e10401c045030b600c288050444401d8a60f03001503110000112100300d100603800c1050114505055004031a40010b0612590b120181210303036240da41b85011120020f484a00001c42c2c86041c50104904407000700c02c82c415000a68802280c0101007044000d5992003200011045810000c9804940b1b1034110001c44000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 894634316 1250 894633066 894633071
    0x7091116030c08070651050616140f0a0b0403030b090a090303060618051210051612020f03160309050d030b03160302220e06070518150319 61
    0x1683d11007180311362029404584e819600c0e00300f01c0c1810b034072005040030403828401d50040f640907484507481160794030f411b00c445004500950a01c001035541c62901900c0040c002c10b403900c43e4981101c0209030346c624200c42d1040040b03401e08000c00001100300f14407032000b004087c00c0c1247d80384c40e03143c4a0b01070001c0e002c054866403032980c1611030404c240d004d130b9000c80c400214800306040040071074903513400c0041000b4001c0c03818601110b190cc010801d50701c00700c441840f805c0f21640003d281c8900140c840001a09200400140e1840480f000a0104042c1c544c4605601003c040008922030024190810841440460681c40c00d103070064a902c002800c0000c1c206840da00c2c3e140c68920a142e0314000070f6246d01412540382420304c151261002500b05601d0030380e043d0790002c0c5560840d4400d42d00e01800141001e5050700117500100042030103082035880504100c40c4c020030680c010069101e00804514051489081c4007030304200011780061501e09684500c4041c020020b440f80c82102c500b034 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 894635566 1250 894634316 894634337
    0x27040b19050c040e09060705030c0d060e07020304030c21060b122505090c030612030f0406030b0f060c10050a02120a0c090e1e19090b0403020709111603 67
    0xd40900c29180500924501d1580b0b40380b40c42000c4c0c01945005102da0411b40014083c810702940040549810140c0b0f16031407605e44031702142610080071607074031401800c400d10080c003003a10303004401030007078078041c42c40e42c0021600c40c03140c004843d248050020980c0401501200030400c258008515410000c2540e0443c4260322802460070010300b50614020368201c100700e03031580301c043d0044000d020654004d1682d2030003c4400f4160300004150f940150b1a02c094490304100a0003140c0e032196040f403d0303e4854ad00e5a000800602040c017080b80144500c0e0000700041c03a0584c1640c0544c078401006000d481c0e0f090841c2c5020f0400a40040d11148d000d002c914035000c0b031011003a01c60302ca00003001071000000c1c0c1c00202100040c3d804420003181c002c00f8400d10542c125044c0803402d00c0b240b40d8001c2c40d20b5014035400340c0e4041e0480043c142d454180c03442c040001800301240114002d07422110401d4645004108030383c540d030040309840c00104020501003c00f04101d9090710301a0900c96540c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 894636816 1250 894635566 894635611
    0xb041211032a010b060d020c030714060103031202181908010911090c0a09030803040213090807031e0e0111030c0f0f0712080406120b04180227040b 65
    0x54000002c1c0706021400390000d001d09010b849003541e0000c900b41c00038001c0c5503034040442e02500c01d07002102405600002c581558400070412120195808001d503e06c05040c0121aa00c4140c280011030005102400c102004042c0d4000c0d5082c03840c503040707280e036420181c90800c0140c00c0c802c040e8180a445041001501d00802c1c0300301246213024899246954114908002803010000d1003182401170900488403001d5118012209480c0d004109583e00e44450000820404680f180300d52101d040000c0d035030412805a016140051103a1a42c541c1c10b00c2224821004c9221080c001c0002035039502c001c1101c0d032062080424801c6c1000959240c003a61030070ba5410042c121035840425403049a518101800030069800103150b09000720b0451a002d07640c540b41032140380b01d444108400200804452034440d8012650004028030030851098075042e10404620b604005030302c52203154203440c22070b0040c2c00703141c1485024161075035015615030b540c800049001070801d609000b4405a2030041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 894638066 1250 894636816 894636823
    0xf05013206160215070f0b250c200906132910050a0807030905010e0105090d030f18030c0c170610060e01020703140c03031c060f030b041211 62
    0x4500203012005450290041c003079410304d030040c00c1c001501c0030001e070030100b1008450203803803076802060000d4544401c8200c0c01c5a081084590a0821109582000c0c0070b8009081c1d24680748100300c9201c030304034044811522810080045a04419900c00042407403811001c5807030011951500090810030050b0a031042010300300102c16800240b512030003071807628580e2090b403080946006440c003480312500038182600602040c05150711160414100310003074024a00910352200200321030b01d4061151a0360700903444e1044046458010201c140c1c0a01c1c1c002d6100320451420344017542c140e55030b0304440816030b15005032020007003403402184003460314580040900c502002446d490501100000300d00e2039a90121007480080d150040c5070b0703600451204102c90300690741000740d00d000d080903802c18001c0c026080d0301d400001001000100c81071400c042e0003840d01030030004592a5000814610a03900010701a2883d030070014002480400300d0301c0c610580d51410a0103510200c1c5040d15 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 894639316 1250 894638066 894638077
    0xf06020c160b07030305160f140702041a0418020a0e040c03020612060102061e180708010c03060f05030d050f070606050406060c1a010f031401180c08010f05013206 72
    0x1c04100103090307800d0503031500441f034103c00c0c8080c16803806100040082c25a11406220030140f014222440854506001c140d400f150b070007a1060022204d0500c141508007607440d070641c8240e1a042d00d620b0043d80c038842d516001c0350301400c0008514102040761030500002803044505d4900403a0100050f01c4280141c418140c80213442041820414000b909107000100019024141c2d6421620f86030300300d124a5800c5140d2441c07080408082c1400036007003240b150020f000c2913007080c80a1b414290301d41c1c454000c40d01032090710824030307407104100742d1207265016001c0e000038402c3c07080000f10090413004018440c45103030000f6100b40e842d0041802c0e11919880ba2012075400b58401043c44201c120080007201c200072001c85940c10640c140610911a000150024424038481c0c6031042d000d5000022035480802c0390141c000071407811020742c9403680a003030300359401c041031500440600c0c0604c0b41a80c0403d4201205480b200c0c520b01c955807120b0800c040c00c000071807991820340c1c030b81500514 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 894640566 1250 894639316 894639329
    0x30506060d020f03041502070b04111207060207140909030a140405301c0e061204141605031b010201140403111203190c21270f06020c16 60
    0x139124601401c1c0311034106202c1107920442d0f4010810040040c040c01030295200fa40500d071071000118900106441c1d19100c03c414400f803144401c007081d02c1c0d0700041d1142c111000c00122499a4510400740b240c40a000d17550400f20b680309000b528030a500030b41c01ca0312900c05d03243c01681081c3c1d46100060f4814980340170b9210f000d032032040b8000c1069680c98600243c20024005140c0051003141860400c020707000c1403810080d00c2070b813500c1d0a40e107034811101d0b6485d803810911900d0a00d401c0c0220280001c0003030fa0340c0f5114407800820309000d110350040440e003004011340000d44030800400c0315503180c5000c580c115583e4044450f45a810060890b000300c0c0240d86500761004d102500501d40081604810700f0740c0b03028002c00081c40074250710407080c04240c01000c0b070000340e40301054580c0d03480b0303030340c21207201c91801c461209012090340141c8410032a03a2100700440e2030428050002465120060f0000c06d1045411000ca003664005100c1c4180c2c0d84110303003021002c442040c01c4042650001e0303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 894641816 1250 894640566 894640597
    0x1818010603150e0a0c030308181c0f020f07030206030a0f0e0105160908071a07140c040501050a0302010e090c0904060b04090b010807091203050405180a051015030506060d02 76
    0x1d000b01c55007485020111445000107100600c182d455a00d580c060a03c0000c00300840040009c901003141c4800e8400108110101d8660250480c04541030301075082001c1c001540304681d44118510001d012a0080802c6001d018030f03c0c116000c0c002c203540300409294045480d5805080440075511a075002104004000201e5083c074034010300400c5008042a0700704800c001c02446103000c042600d8044034860b02d10410032281c420411071032409078844c013404484080303500c0034195a01103007290340504100e41c10000c1c1d81c2c8420404c0f582030f61030f01000e0700240f0b80412882d81410f04003007642d0008004146213041070f800b840010107481c0d542d004000380b0302f00480c0c100029540780c000d6044101c424240103410b881c0c11640104dc411180c82510007a001400b403481c24540600c0c2140c3c060b15000e0f000c01c84520704900d030000440c0b01036402c021a5413420f8002042e0008005d42c91090b00c0700031079a41d200b07a9202004401034400078215544c0074900700201025071405200070070301c030180c8681c035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 894643066 1250 894641816 894641843
    0x30f0908120708011a0d051305070617091209010302090d0b100e0a060b030627040305040509070207031709180108070f14010203191206030b0105030d0e1818010603 72
    0x3c1010030306038030000c0a04490348040d002c02012009968401000110004540d621a00b10210f8051039140c050043e0041c2040400d0880d40448501c211010000d04004951078141c601c4d5500c407190301d01400c12500602c2907000d1507200303030014100d140300141b4000c00c0c6243c42d100c286d040c0106884448408440d9a020890f6211101a0551001c0300200c200304040c580007002c80766100081c80248142c01e101608140e02991014040204030307442000201494140b80180155000d4092144520903040005111510010341001079a80c031040500000d4050041d15440b60411034160340d02900740782100460410220b00a802080110000e14035145043c508080f4400c46030001c0f0210f00c1202e95096181c2d800200f16030f010b10424040c42903004208000700c0e142c4000c03847c00310013181051400400c0c4440c61955a050322000c074140c90403222650029115800750811154001541c00340c03411882600d940200d501840e000c1042d0031071a0072400b15401c590090700115440d0030b002c0c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 894644316 1250 894643066 894643081
    0x170c0d080a030f1514040e0a1b0305060903030417070c0509091203040f030e0109080d0c08270a0909020d080a02120d05090705060403150b0a0b0f180d0f03030f090812 73
    0x710441700e280d0030350b400c001400400140b95207075266084080c2c43c6e00300b625200304105c64680708400045411000342c1780341c2d00741255480d48962081c0d82c107561003903440041000e1060008115a0282c1c0d0084c03004400e5460130060110000c801030290382c660280004000c00704542d04006c51040340b003046010901600782c03802034135012405034528104000141d01b8030580d080082c5807405502d42c0e08140b0011009440c28015511400800340c9290f010013040d0f0255414258041c07148000440b41202015107519088080b11220310001c1d40c0002d604000502081e01540108036096182c419229040c3c00c0c2000c0c0340c4503034060200c481c007096a407010080c90110910034140507200c00c983c0240380c940303180c0b00c00804d41c0c4940490146140d65a1203c011580c8048401c0001d1100ba58025222000d0a56280e11500052031a090040301e00103a1f540c640303404800340542583c0301811011810340da44003100101849124001251340d610306c1c41b0081440b00c0701130483c03038820100c070404500e030154 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 894645566 1250 894644316 894644339
    0x60c06061801050a090b1c0305030f180307020d06060905040305031501050306090a1a10050a11010b0a0e0702010603080f04030317070f1d090907170c0d080a030f15 72
    0x450000d40a101d020040c086a541c1280c98400c035030308500040ba00c0c4000c05c0001c0c003104464030110000d140c0007401c034400c00d9000009148110803000e0803500701d0381ca0100016520304441c0e80060300d500100702900051514148032141c081c002e031400940103444440e00011280155429004500080200840b0310100e2014507000c041c2880c1860650400c800411010701e005080189030075101c4007030722801c5489480c0b8800400b001401442c62000501c00a049a48410003100009503070501c3d001900205010707054039403402412404000d40388c00401e400c000d4000c1c6c080320441d52243d000001180c4894041d110809081100a030341e94614500600320390300400c1e000c07000120301c0041161081d0402140d032050304613400c0044003100a00701c81d101c0441c260005581c84090300003800403280c00000e8580959043c20064001c010403101070607510001c004400d548441c0c03d00346600000c2c4214040c10030482d4038117020481c1c010341e103246401e40d00c24040c5010700502401c02000018940c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 894646816 1250 894645566 894645589
    0x90303010f0b0c060a09060905120a031401031703040302070b0f0405090609040b0105060328050402040b01050412060b0d08071113020c060f0c1b010905150c0d0911060c0606 76
    0xb4141e0a141c41422051a500c0e528004c02c0c6604059407000d155051180b15042000f541d030f44038080e1501d03580001c0300c44c01e030b982003013075044000313440e02106021106683c11203d058980092030050741c040d030021103000c07551000b007044003103000b41c0000107004641c40000e0200300403006509901c1e141040c0a101003d00c0050800348100502000d02c00490301c000c3d030b401d056a8042c1c441c03075940d44e9226100603e4802000c0c0071200080143c09402c16140e055128a00681c82281c007406001510401110700740503500803804000e006d00709810004840754001c40540201416800b01c00d8004e40320f410250b0402101603c3c81210950b0100035440d280b040105071564000007182004401d95680e69140f500400c0807042c101c045011690f0403c5601c1030700c03004a0070409840b40b07510307005801030107840000c0084a8500c619540c40180341100000716105100698089043c207941e0b0403030001621b02d0446c1a6001d0040080d0110181ca4240040c04460100d01c01081c041c10311405226044502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 894648066 1250 894646816 894646829
    0x60e16030c140304020d020105040b1b06100e150a0513020a0e011805040f0b191d07050d0513051006050901050d050d0f18030f0b090d0e2106090303010f 67
    0x341074240c0308030030350b015290880d8050f00c010540304490710050728644500c2c0c20203240080c01188850301049810445c490b008030b0601a00c00548440c0650301e8618005e00401c583d0150f5007002541c070340f04103115880010380061104038100d44e100040340040f40564003080c4079580015003103424035000b80346490404002e1a100c28040391820240210201a0050b1485903480d958180ac0352012030304604540d02d402801030500c202e0004d48900329480313521610f402031060b02182848444c4119003140b044c0881d417103581c503044018560800410006080c20103109648118002049003004804e0b0324007210b0f200015081e0030f0a0801280c048140e0182c0c0c85001d203102008001200411443c0840c002402d09203250046158150b0b5502d64030b100c9107032907140d2a8000000d208100d0303c554815070069101403c40d8540c0d040b480d03218000c3c100d208021904180741d81449052164480124a400107825510700100103c2035007400b0080e04e840f540c03603002100502441c54a07a41a1005154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 894649316 1250 894648066 894648077
    0x909130503041e09020406170a23180a060204061d1020030a03020d06050603060306220c080f1504030905100e120a0605090102090105031504060e16030c 67
    0x1640d1031a90320310582c0078108040741c4154076070350801c614080241c0685002031040d9115511000d000f0f040c1034080340609401c982000115228903440e00c150400d00c0040c1c03d0301c40b401112001c00034102280038110303100d1040e01304d441c010014018002542d5981c4180800b5a845c0d18000004000c480346100440404a05800e4001c0c01d90751010030001c1b800c0c050a04100c3d0020000c0311541240003100154030502000511105007603260f4000c041020302003504200041e180c0e0b0900c06140012200e1582552044001c05c42407000240312031103940100c04400003200c2140d4403151894001c0c1e20030300c0c03941c1c01401c07030000300d070014810941108000501c0c04400c0c038040c2c038010b25010701c52003481c0c01070700007101c40bc05091184404005429001d040030108030b4200c260155144008401528503601c8c0401240300c01c6418004c558208005079640c82c119200c54081d20404403400e4242a0b10642d0b07444001000341010750800c0c8070f070b80507a1005010f0201c3c00c001074142c601c0c04040e10100b01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 894650566 1250 894649316 894649351
    0x80a0c020420160501060515130e01080d230705010f0b04020a2a060603050c010e04060602030409150305060103051b010c0b04080c07180905010b10020703020603100909080909 77
    0x400b5205032050f20301d00900081c01d420550901a0040507180c1001d9001040800f05080d6800c2c900c0c001c040101c2044105160707540e4821264001300020f01904911f500908000c500d0a84524035000450211038070400744206200807448855110503030881e013994560512040c1da80b001c0c42110201c001c01d81c1d05600c1d00c0d440000050040254059148104e502c48510204130741c41e42107100c80044d48042c08200203612030030050b5030f807400480568002903009440c940d00d420140035200442d1400d800450609041c5800d000c00b814000c02d031385007281000900007010400420034540218092406052418940d144401e0140a0401c20b641402030b081c0d54500061003c11a0940c06600300d041035465540403c0340500b40b003503a80c05007041d9009124030198810203035115400c0079101d10001c008140c0701d6020b100405191040ba0005a048030b01d040001d07040000045502c10140211200f40303913141c0441d0800c85140b2075054540d807102045003030407400c1204480750880e10205030780c940003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 894651816 1250 894650566 894650621
    0xb130f082a0f0904081c0504140c10031e020d09051b0a03030c02040e011a0315010b0a111015030c050405190c021501080d0221070816080a0c0204 64
    0x1007000d8601540500d80d0b0307800103070610405d6003da40070b11005000704681921031481c10320203818240c0e41940c203c0510155000701074400034003201c5907039010b464120141c4004c00305800074600210091600e41a0380756001c0c0703404203807000f8021640480800030b110800c505206107464030b100d09220442803000300c1d502d026070ba241d4564003120340c10720380351590030307903034400f09002c3d18840c20020134560034003032400c0f404241c03601c04240b664015401c650714064210030070000f2207070a20030016951030401c14408400d202d110b181710007101641c2164008007032040800b040340d280300c04042e0841b030000018020000282e003150028101150305001c942031000b861001e8a050500000d1640d550301c11801c0c059001b800f00002403180c0c035036610415031351603d6254450031088025030060244e01c141c04205100c0120041103118110750850401d4065030b210a0140e1150b00c02c2003405200c0f440110014048000410200700c41f80e642d0900d81c207440c1306220980307005d0b140098900120000600c02c0c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 894653066 1250 894651816 894651829
    0x129070f0b07050729161b030915090f120218100f03030203030615070b0103031110020a030902010e010807050f030c0702090403081e0601090b130f082a 67
    0x41540145907900d00b52a20081034855118440004061201e501c00c44004001c0c0041d007030042c00120301c0450322035618001d054820354815408400841d03c1c155694020005187d45420350038406d00746014216291400500b01d580340300c1d00100001c9148409002030340c181d105220044c50080b0604100403511b500180e4001c000300c2c0d48034000f0180f600010004030511804900070000c1c040c8842d030207501c90a0082d1a070b801215014010b040e5004a04d2010b0b0700c0c681110809a00203507040d205034215601140c3e400a600410076080c4524a40b04c1e55031a05031005018003012a200000c000b8424400074004480814005042c04030000030407040741d411408076400c041c1040d4119550360356440d404d80c498041e102c00030b5088030240341044201604443c07103900a4582000038210b242114000900020341201c1d400d002803400c0e90204104980e400c00350040212002003c81c50684526002e03481e0002e550140c190303030b40303c281c1d401e0001c03201808080074800001c403861100c02240740404c5c0c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 894654316 1250 894653066 894653093
    0x6062402150c181f090812090a03141006150e03150703090201021c180e04030c0213021e031006030204080a0807020d0b131205030601080a020c0114012907 68
    0x40811445440303e00e070360760165584035202460b0481c3c0020981c056000713221545500910711a4403c022015000340c0c044000d40300300d42c0c40180080d01c62825036072540103588010310301c403800d4410150102444e981c2c60066101800100d14100407546c510100189071540001c0164086c0e00030b4015680c00740c0c250340d03d4941c015100d0030045264400d81c80103c0c039040808040a10700e45d41142c08000865008483c00003042d01c040041c844291a12819100800c0695005011500c140100001400c01051805487c00704907401820800e08901181e201070720143d0011b01c0302d100004214084003660300650251105160840c241818039902c180e40709003410018085200104400085603034400030740e0202613000116001c00e0a081c070325080700a070082c004565040c0d120075516205845281541d100c0c0070142e58a101d10b84491000c2802580700e0a0100308030754882e90100601e802c10b01e900b9000f05000810700c1c689401044281c251030f6070110a41e5000c1500b00208004981141440d22 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 894655566 1250 894654316 894654337
    0x60e010e04050c130305030a02060105012c060c100c0809030720030109050f010501031703062107051c02040507020a020306040b0915091b01031e0906062402150c 71
    0x50b10391100b4900840a000b007600d0700e40710603504030b000320802c01c0c003002400c21001300e1780031650030713903211001512100f40505203030070618407082c082c6058651340d61821030b00e03000c06400c039854158080200c40c140000c0500603030701607854205540c81c4541c05904541c1c4480712740003031402d1464960328880700d091541d0004105c00b03e0801003241c2983c007903000b0814a135000f0100c440a41502072964041c0030248825100015010001024826694116441460300400c8824480603c81701e21508004411205040303218440010659440364058100303d2000c0300d00094034100c103403041000b5170394010701d080210340240400d138006031000644a60040c2d403003c0e202850346d80d4403800518120000c0f681da0203814414003800b40d0081d000c02e125882402490003920765240d220010740a0760803c0f0105040600d010b0030440c2a1003190384080e210070b11030080070a48946d16078403444141c842d03810301d00860301c21041803414107030104010350203000c0f0b807070840e04d40e0b03d4401c050700420b0043c9030340704 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 894656816 1250 894655566 894655571
    0x1051306030e0607050c1b0f0a1d06060a14030709030506010803120108070e0106050c0c09150405070e0603010501030906020f031f06020c010815030a0c0305010f0605040e21130b070c060e010e04 85
    0x4021f03035841441d8440d91400140c194011150340780d2002c805459904400142010fa0001080302810702c601160111240c40d201d8a8450a440c80700c0d5a0329031005010b00100407050b00d020001a1051020b50b00900602c4003c0d5120041b00c0c62101d025801030307002210642c803100f01044110b000c500038904507949410241d44824044070024208840c10802540c416014000c000e265007800340509841c0c0c0c0240d80800050343c545500703581a144901155502000034001044150720a17045080324038840c00026040500340d00700c801080c2c2041d21504030040c01400c0355603910701d10b00d40300d900400d064401046080010000a41820783c090f00b20700e486a40b491110244d41c8003003045424895100110300821030341ca00305a4020440c0084140906003092000a01c40c6868040c1440300310510000d000b0300740103181034503050001130081240f0b240003882080180455850301c4401041d006096580c2c1e40e0091070000d4101c08250031420501c00f02c0860f40318280d910222204c3c2d4040c05a800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 894658066 1250 894656816 894656863
    0x10e1c0e0a0b0d06091a150f040306050a0603140d0c0f170307201f0f0b0603070504030302071d040f03091a09041512080901051306030e0607050c 64
    0x128110320031a40040c2c0201c24001009004000701d0b52080084401c01c4d10104014251886803283c0c00140030703c01c561107600c803071000d16945c07076000003803030001085800310703281940d0f03583e030203054a03401ca440701c0d0b1040d0341341020170601023800340b0004031100c004080c0500b0390380401c000c0c11425010038050180381da6406e140081102d8040c60422101501c1d0400c2c1d160b2074103440050404000004d840c205c00024002c1440ca00700005129400000814900250408048241d0300901d03208001f210031070b0716600d01e4202c545503840214003503151551b078603503a5419810064079049603544090708c2003103040c6041508171158802d15401c1540031304600380c00300513402c0032280014150041c0c3c090031040b11500711848c41c1c1e03500138280c1340c44c15281442461990040b400503c00c651088401e40c4012521800004501100501c0103d070b05050203801e204144101d4400150544c2296000c02d581d4100d01a0300001000015881030a61071700b54500918130203000c0c7c58400110840c80d004006600 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 894659316 1250 894658066 894658069
    0x31b111606051206130509030d0605030601050102100e150f0f10120213290f030f1c020703080a08010e0f0402060a0c03090302121c1103040314030c1608010e1c0e 71
    0xa504801c103074011700500a505002e42003a4587d402440f0380a41649400c0e80003400342000700b401d50484605802410f02001801d1280d8081c00700104141c42030302400510341c01c042501424a80140c0c8070b9601441a40352900d004d0841040c042c01602c0003000b004410031041041c40304c01c9132500da05458141664000c66451005052652070801040e12040b60384820300340b0804004a49440440300c00340703010680070038582c0301c0da030242070309006410100d5144500d000002440f041c903280d510480700d0040e80d03a10360800c5a0040e144020029030248010000c02005421650700070001d000a02c1e140c2c24158009440c0c2d10075840e0550520100507241000e15004004160081d80c000d054009005100c0e064252908078031685180c403e11905101c800d541d1145400080c13100c109401140f5084c00c5480e4450501050b06818816101c10440b10001080a1044000f645035040c140040c880c205200d090a6818210f00c003003041c3c0c4001060003803100d051030a200070055174144031108000c040c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 894660566 1250 894659316 894659329
    0x80a02033d090e12070807060b0307150f120b030709111b010603030206011a0301050f0a0803070b0f0c0c03040b0c0a12083c07031b111606051206 64
    0x2581c02801c07080000040440340d640060030034915020560744a00c01c60301503964a809041c0e03014108038014040d80e0000b80440d8052218441d0040c00c440c1515500c45d000f441e4500300c2c800600c0012506100044102c1d080107101c107851454080c10302034902410007280d03031401e0600c42c003099281ca40620058a89092044951201c8441c0c10350400c40c8000580383c0c06000d140c44101c0051040d03034000100c83c1d41d180124200301007918a440c0c078503481c00d01000201201340c1c0c0d8640e0b000075144000030300c0850400081c034419220740c000840d0303440c001030a910f614000801c24260708504010410940c0408000c50782030340d00c40c0100c161110080710005180440401c0000c2000d182802c001c1121070304003e41c14402c1d18050005501e030301300d801b1100e103c1d411200d04500301c6e50564000d008480d014401d000c0e0b01c1a01071900107003c4040c0c82c00311545280c0046400041210450f4540410303c0502013a154100000000000285401c0004000e44999613030400a802414040348103a520f91 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 894661816 1250 894660566 894660661
    0x3120c022b021018170d05032e120312060b0f070206070c0816090c03090305090402090102011103011e0b091c4803210e03031207080a0203 61
    0xc600402140c541207817642010b5004aa10040c0c4920204101154810b030100c0e84120901c686032080341c0981c103131361481c180340b003400440c81c01d4070b420000c80d0b1031000b100d03103002c5940259580b07000d030840b0401d00004c880d036542111019040802031031307811203844070859485e13950649040355a0366990a14114421040e0841501c81c0546200802040c8010800c0c6003540d1180710f0400c02d040c00b050040d401c4407440354000307004c64814080001c3e10314055004c3d180ea50010b000114007506500218a41d560003600f14a07040d5210203001484103940c4070b402070103440941c0c01c403481d0100d4840000c0110701c108419004000104882104000c0a001c90200c0f02c1080c200c04040440c04000380c07007202d00c0c070208800201141c20b5006403299011001d82d4100d0b0b401c03482e80241c8445052482c44186112024038061046014544085d500d0801c000c0c91030783c4060361608041d007003881005241721405009201da05005209201c070300c00589002d540e010864200170003008400050800c10b8000743e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 894663066 1250 894661816 894661847
    0x303090f0409050a0501091a0f010302061b06101a0319020f0705010203101403150f070c1a060f0123090d1a1005030d02070509060102030403120c022b0210 68
    0x1948140750401c9170540200000d43d00c101035110003a20021004080c00d101212980880c0000500400150520702d00800304030441c101d400f40010040e5240f646404001c0d00c10160308801c5410800425020445031400e41d00303c44140c528608103103001400220000303ba10144550024a15203010a08800c49804c5030713024000355281d02e4082c118103041d401c9445525030200d065183e0301c81c18680403500c4520000c520424030103d4660700744442034050020261030610120f0841c1802242d0701c60700d07900c4d0840b030b4002c03242658900182400b03076000c0043c0d911410b104120059040202d11070940d40680c00300e8405c65a169603c200008040c01d4444a0103010070900703501c660f28041c0041d9105200d106071a94001d845030355082416644c903800c84201c00140c208500c14049454075400c41c030303000350051046900f460f84a40381c1c808888044d800d0000441c500c500400700b113052007041c000104150030791020051284c1c202c0d8903100d00c03030418002e00c2090116454102940a001c5007201000c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 894664316 1250 894663066 894663073
    0x504150306150914040203090a0b100f0306051608041736031b030c011103071205030907050307030f120306080f0a1719140409020a05040914060303090f040905 70
    0x8542801030700e40000f9000da0f1301400f0b003420302c142007800e041c002c50b800303021880c000306220f0f1039075202c2009042d0081c000302444400002c000404403401030030030700a90301810000600d0b007000f2440c00903030b804010200c000d00c907128041201007102c403488441d585408120b529070700e035440d40e001100c03c0c12070004a00c01d10034401c4112401003100c0360182d44240e00780c0c22a41c082c03510b81c82c0c00c0c1055001c1651240d141e0300c0384403400c105520602c002601c05422008403404c0440590b82d030f007007031469030380c0741c400041d00401040616801006202c00400003600076040f007e055444960302c040c2080d502400c4d0441440c04d00240601c0313680700700010f0000c03500391205518a017003541d483d5141003800b500c05541003030b180500b20106004580424100b08480d5011000d51031060710710011a059040c8a042c0c2440000342d01c540c40d00060504020350f0751340301e07500e900b0100448101c40304411038500340e01c0c2e508100301d03180d00c0010480700300110880d841c89400304858000742c080c05a14000030060300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 894665566 1250 894664316 894664349
    0x3030403120f0c0f0e0a0e0c070f020405070e01081503120306060c07060f090608150f0d060f060512010e120f04050a0b0301090b0d0b070f0e031c0306090209010504150306 75
    0x103510050000003101190741d185e101018202c100301080c01d240c060701c01200020404030390f002952100034030005118051a00e101e0006400207000c80e04202c601a0101c1c4415a196a05692154035187e01c904c60480b00c0c40940700c1c102c00f20b680c5003003002015082070340c004041460340c0d6680c0291200c0404d0032080710103a0751100c00003040c0c0c4102c401e640f001310ba01500042440350060601500ca2800360384000003072041e82e4100456100c00c40689a0400712002200000c02d81900841c0d40400e5002ea01060403460035003802025280c240d00c042d074a0f403511200c880b00d000c000c00c10b201c1e103100214a034be4480460440c030102c1c901c2907601690380030701000d10014070310740c41c04d018604858180c10100807511102c2d0510100d84004d010062414040304001002180203030710140b602001c0f0f03d840e441700003100c40800d25081700e800304c00d20241d40904662801e030307605029910144c18014010360400c0106000070b412405103010b141502581c1c0c81c44400054442e502020081103240079150a04 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 894666816 1250 894665566 894665591
    0x115090b0a080d1d030307230a1a0a090209010b0a02190f0210050904020a0206090c0a0608070503070c060e0f0c0f0d080306130501121407031707142406030d0203030403120f 76
    0x36407180c1520100300740d0f00e0004070b00104020402080d120340144c070441c12030404ac000d008507410024110031010390740d5a01d50015031200550a4080d001004203681c0d203000d00307040a89040c400310f1140d05441e481c0d48182000444445480400035416540d0440c0c048100c0d2054982e401550354460304203102048403480294006452402116078400340c94010080c0020301103501440e0141a0101e0901c1001c264454401c00c010b51f80494a07141018aa002d5a99281c040d196036100c40d1200741d004a182a08030f02084c8489142c00c903007216000c510000300004545a0030740e01f480030342420030200001e80617440b40403454100d04003800040199603141c2c091184514440318050314540d0504c080030340d48030b40028407401170b650061144049840d4140600580b41d010000131a98580c03001d488450b484801c011020011015403d480c0f0b1381c1356030340b4102900c1040200010700ca6403202c48080d4115401004170382d006a050302c0c0942a18103103d0b41d0708081d1801e024091115454280031410a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 894668066 1250 894666816 894666833
    0x9080a030f0e0a0822030611030a240510020c03070e0426040b1c06090203011a0f04030b06190f0e010e07021c110115090b0a080d1d030307 61
    0x8094410784104610360310200c00782d945510b0110010296401000a41d00c0000014186000701480c800e400c42c4a544075aa14802d441190144c010700b01800f0041c48684041e83c060551015821698440c08441e58212854545010300c10140208000c88580740700300c0c802d001c800d482c2a0040c04452401d50340e0f40c0c2c502895201240d0a503085c04580c5401c0f64000c0d0000c145040400b0301003041f905107400d000701a001548090307400c0c4270048031202056401e03d0a4020000200544000140c907989000c0038131505084000d05d40d0801041044440811403940781030f1000d403038000200e408150b69000206215020074400301580341300d074100014021145004110170340300311440d9685143d9031840c900c00300b80c4040d00d81c2d00140e0000494020b074100c200007207a601200713524010b884003d42c4002d950846130700c2d80c00040c6403004100180300c6020301e07008a81c174900058030314800081c40c0015140e213440da00d468400c00c0094920301c50941c005000342008240030010240ca0f40d40c0480e103400f0b202c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 894669316 1250 894668066 894668081
    0x21f0201050c030c090f0d140f0601050f03030d0903050c100e01272a180b030a081206060708030a1509060602030703050d0e06010609090b030307020a0506030a09080a03 74
    0x540c2401c0004a40c000140d098a008550003442c40f410040d0a2041014401d2000e60a540021060741c0003004180140c117405107150080010b042000c5032000030307609259058000c0780c06000d40e102c02ca038941c0c50001c112000d9101c00d4a00213035481140c43c086a2a10503200208214031401d002d00b05092025400642c4100c4004001c03c490301c68402c036080621842c3d2000d601c552002180b801c0815001039489442451640243c1005c10010441c1104031030560060b603201d0800c0034280c109005103115090500300110001c21a003020303580d80701401d02c0340344151300c00c4200d801d020480035241c07042500d60b02d0354004225a01c1e4078140030f03143c004181c3c6148281140c1c8035620002078141191003608213a6030150302551814402e0380301a55182e011f070160303a410907540d03030401c1c82c3c240b4140211806843e465840d0f0080d1840c04002e00140c0e1810408103101350420050303540180c0d10200a003040311000d60b24541c40b0355444903940010102d9410152074050002000605164180e0140701c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 894670566 1250 894669316 894669379
    0xf060112261321110f0f040f1e0203040c0b1e030403120b090c191205070f0215070f0309060906060b130b0403020609010804020a0b0d02042402100b0a0302 68
    0x850b441d464203070f1282040300d50101411280648520000500300f400d9010860100501060ba0038040308012900700e82c02640ba842e09180d5900b00c409030500514405600145500800e6041d81426243c400f40c00840f441483c04500002aa01e02c10400d082c0d404c850000b140d4100c9074891501e0b003001340c245242c5011500c00c840c5810102d4440c0c0c0b6000c490300d4080c1200c8000d560504051a840a07900d40100c40b56900707000c41b05644913000162030107250711407601c0b95101880e47d8040c91006c3d10f040503003812030341c0503a10350301003003519640030000400c20300c01480c000ca801a40d9090078001020034941c098a624100300001c107480444500501c022548030004024160303075005144c125000ea404029070114007008030200d9984160300d5950010700040c0310046080d9141014202c40d48031720aa21003a68010400300400d9460070038100321a1254441c0c1ca803140c08544c8002d456807a149140183d0aa40c2c4150004545410880d48060341e400b40c103ea80190022001901d070080c462800c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 894671816 1250 894670566 894670589
    0x906010e06060a02071404020c060c07050c18060f0d05030a030912030606050909060307050a03052401080607080c0d0204080106030b10120605070c0b15030f0601122613 74
    0xd01030b070078428101c1d20150100d501034400c1c1400c24046000400644400a9210b40c081c041b02c0340ca080c2c18001c05000350030007815107a444000d403415504060303c24600b907104801c05c84c402000e200d5648081544514219210040c00140400050f5003014401d8040d00500c0085580300403607802d6030009043c04d0113420a154a520703903c0301281510518080c01c0001101803091031424280400a642c01c5030008042d20005503c800202d00c06100c654004d50301a408201d584125484040c0c00d06800043c40c090206a58184660380c1d81d81d05014141000300040319000598456001055848100c540d4206640d0b80307669610950181c039040c0020380d450615140885e80451007a83c0e048202c1d089019001b103124020307140c503002802c006288105102750b886001001801610310280700f21050415940741d00e640c0070906191980d800500c007650382c451001403043c2840a12549200b55100c001c0c0611421000f100410321114200180c91302c10f13000c24200140420100c06105503404403038807 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 894673066 1250 894671816 894671821
    0x7020d0c0e0411151b010902032a0d0b070c140105160801140a03120203040e010308042c0a0903020106080a0f1202010207080a0309031701171207051c090e0906010e 72
    0x42240009042c514000101070800088170301c00d10343c1c0781508540c0060800000e400d22560082400c1c240c0c0c025091940c094105900b0350214a6085240e84110040d42c0000c480140c5541c4c41501010180090f4180700ca140b01c5802001205202204191240d4001340020f00f082e081c1056552000e030980c0020913a00000400d400081e55200c3d0038144005000044031851604c4075940e03c452080d07039100714002008045243c101d80003070180210b2042c0c0380c1079900c5103410a2806804000307014441440c07240022071803d450401c0d05150852101c040026070481140307010b80c0101f00d543d0040c26213000b01c04044080c003803030a40c2c6000c2075004140801c04103035108000c900300c3c8601500100152811300003100658800d9016881e0300b40703e410140000341042400070400c03072007641b100e8061443c04004603400c80c42072200801456070348454500340340e8243d5817180c035400c3d10f84d02c1e10302115003105500d42d5940300720000001084400d0880080381410540302da151003090081491702c0e00700201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 894674316 1250 894673066 894673069
    0x7060c030515120714060d0e0703150b0102100209130f0b09090f060c03181e0123010306050408040e0f15060406050d0e01061d1005090603100207020d0c0e0411 70
    0x80c1d45100600d080d010388411401c1007444017852001103007054010005000e0107058505c0740c4201a60070302c5100041ca00300b40b6500d4602c0701c1400c1c1c00656100d0310304000941c0801e90700011740ca48070703452090303000d61680d505801113040640007050348034200b801c04103540644003155001111100c010303500316156036034200702e43d0795039104110390b018641d1000000034100202900a150090805030700381d4549000c02d06c1d86850402c21485040100c044030305100c1d03584500740328481c01040070018500c800441b95a4002c90201c05210250900d603c0704006820040c1c880304640180000c05044c0304242040d890001c0c150204445150b00c0d0603a00c40500c0720340c508035041d078003121000da440a00c1d2805492211000c0e100c800b00320030242d9214003002c40c0840700c1c0d0380000302d01c07404441c0c420824606050128084015a8001802502c400301404a1a2004101214900c40c0c41c4405a900c100c4d502c0401c0c460b0b848120090200100302102050b070041d0210824011030007614214004d018250 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 894675566 1250 894674316 894674329
    0x905010b0409110d05010e162c0d050102160b01081504030c21050703080a020c030a1407021804020f03060603030a030b1f03150812120a0207060c030515 67
    0x500500d40c4003448100000d0744503030040d030403881d031480050381891240c14145042c4c03907080c0c00400507030141c4001c001c050301c03029100e585100d00520384664000300c2c0407154080d4001c8402d0316040740c0002c11904081d44c070f40113440c502641e8420001c5689207440010380300b02104016040310800340d160000507c2e80c0e000600c82ca2111099160b8100e152502c3d501520321046004081b0b500c9202010381e01d008a0345000051240300841c0c480c259207039050700d801800e241c1c0c000c1240b490184140041403141200000307403900c110b15801c269100c1d0200304282d01c881e009180d03000313600c203040d004903500034105400c895000700e1080e075854501681c00c4d0101500d640d01180d00981590040c0003030f0140500c241c005070420344015240b08440011110b001190311400301255012986030420026607041200001e0001d000b0400a803800036035007082890248541c4410745c00b0948c0c2c140c003164541402e5070489a507541d00c40810001203241c85409005410122290211541e040c0882c805d42e08044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 894676816 1250 894675566 894675569
    0xb03010f08011b0516050105160e030f030a031d010f09060e191b120b161e120b1315090626150a0b100507110409060b1810090501 57
    0xf2100d916405103851048802e40c0003400031601500f17840c00c11001040c020b01c205d038001d52240b03181c802003c2c0b4507480644a55000710200d0302a1307121401c2c0108a40002c4192680700e0703210720703011464800319491109065035078131049405510b0300800080b039416030b90245a201344901018080010300c04805910f5000144141c0c030413459665020700000e45042c00d0300504840c0c101d09119040d290701405c0780800c1100411031795400c0580174020100d4004220044074515840c0c1000309412040e1411340c04018060300d50b00748010620f0780b00030b480841c0c0200c51945d80c05000c06040f40032106540c0c02601c0021400441d6406410020801049a009010a90b0000d55880c07617481e0300101e142c3d2010044080c20380c0c0d44c0c015411103984c50300e0b60102040c0254021000494024103a00030080300d4a480a8078609005041250100140000c0101c03212130780112400070b000c0805007441c1d400361401150f42640028a20002c0060340c4c02055400d0144070740303420264032a1f0725030175064100c6100307 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 894678066 1250 894676816 894676841
    0x1d03090a1401051b0f0106061d0301050c07030305151003150b04080c011d060f040609081b09101701020a02120a09030b0c13060504031104090b13030c05070b03010f0801 74
    0x3005401e2013082601d0303c495400c4210401c80e04a40d449400e80b03801c58140d9009003000a244480c4042c43ca0001e8002c4142054200c008120604220a1036242032085510040c281520b41000641c00c034400c582e88001900040c240301e05072015644018010611f80801005481d2024004070704aa00c010648090b10780f40c00c001d110f1718151308010746039501020b0351070101540b00c4100000720b4441c1d6003d4551001414003441d10f17907050680140c07100025070403101e240c3c1d1100c5609140307088034034401d40401209450440703031500c806a41c3c2642c7ca4050300b000c000041d0721551403031070000550041201004650a490b03041d088280e20b0000c5206004030341c0d000800304801030010654100500350061603000340c06182c90000c0c902c0300340d0301c509a40940702048000c5410010b20001040c2a403003002d08a90800003085150b4800048000103070000c1140d91b0746c100c0201c00c050003641030307040d661303040011520f40c40c2e034441442045a009004c1d00e2015600e40c0030010b0100414014122541c08 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 894679316 1250 894678066 894678077
    0xf1b0215070602090402040306140901020f071103031909060e01080112080a050c070e0a061409070807140d090c080708060c07111206040215040602060c07061d03090a1401 75
    0x480c06000409801c01c003019500c0716801c1000d806070741c0d51781c0300600c011842201c0c0030520756004290300183c100001c018811690041044c900802036500407074001da44d2080e14050644035074008285140201d52204443c0000d00d90011041c5800036440021a0000d950b0b45030816040e10044905034020320842d09002c4059540e400011240c0029102c030414a10301181084060a0014580b81e0319500c944046c04030340d024000d000c0d0b81402204090080a40d029002c142144081758075400000d0a040801039298003003804240b0482200c2c121128a00041c0e44070b5600194100003001e4a060854001c0c0d50f4250004800101040300c004541c4d00002518459840052042d45540300303260440d030420040860300400d03603c0f124000312002c91031004002c503160a2040c001401500101e0007102c01d000e11007080202e900050282d44050101000b5072180007500e805800b5012030f030074a040b000c601556082e0000c1d0000042c120301c0b0011200e8110701c65803440c00d18503189508404600241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 894680566 1250 894679316 894679339
    0x30a0c1e0302301c0b090603031909090906050f070305040816030c060219030e03040810180b040b221e0f0506090d02011b09061b0807030f1b02 63
    0x1d20a0400745514440c0440125246014003001c03e03d42c089203403100650496544040b03134030600c3c45a82c8981900342c51402580c10640c00180e42e0703019500084440036840a40441420711554141004001c0c0031005c0c410000c0c02e16004000c2d2500305e0f00c0e0080030221200249400d88240181e80c012600000260310306070104003080030f115411101a402d200c1d86021940020720f0920040000c24850300300c9000420140d000101551510340c03001031668002d000c00e100000001c03808002c042d19154001800007640101001000c2d4034540241003031451004100600040302e50841c415045040101101c000d00c00c1720748013a40c0d002001404910140e051034400040501c0f1a04009000d440c014407801403658402c1d01e0040200d0310603087e608110403031000f01d5024001c6400c03450310316440090300407500c0001450001c203446520100b080402c0710584026200c1700e03d02010f604030000d103980380014100a0725200315414200c0c0015410f07003118140141c00d010351042e11354010000c09410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 894681816 1250 894680566 894680593
    0x20a0507021c020603131103070803041e150503101a040909050a060c0e03120c1b180126030304020307050f030f0106030515160804170408030a0c1e0302 67
    0x205201144040300d500c030b070a562000340c0c0d6004080c5200c0d50a142d9911b00d00c1c1203920b03107041000300c03030441a802507100040c1800041da01105680941c3c0007403030038800c4561824882a0a4001d50f0300c008101c2000c4800c01c10041e41c403800440c400c0c0d10481c141000d5594440301c1200b80c07004202e9101000300b0034030060041005035003012042900a40450350f15840310b8032194119040d5228582c00f18100d480030803440c0c02c0600c0b401c2c1414541c031400c142041c1154141644520340c4403489628270004001d0407000355160b011084086100c4040200c0c9036866814410300302160f20300b100030004081410192100c000802c480c4540c2d40940030344801458003003440f00c0524040002c40d418051604545030b0034900b4440d140c000c50160008009a180b031103900a44050050500348041542003800c180441d00001d16540041e4406d003c2201c50305e107480345031103600850f0000b120b070303000004100004551000f10716941e076001d0219030170394088984c103620711070281401c01009600702c007051044a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 894683066 1250 894681816 894681829
    0x70f180b01051b060612010c080402040509030f0708090102010f02070203031c0b04022808040f300c03030f022508070c1806050d03050403141c21020a050702 69
    0x1240c0c0c040c14460b04000d0102c8100d405481844222290340d4400400c00c0800d24021a00d02c2581c40080000c212440941c0802032900318000c1001e406161901c002c60003410041007141e0690b6548401680c4803900340ca07024245d0b41c0054403260056091000e04142c00d5540c0c42101c030ad081c2d00034000d40c07600b20740241c404128010200d0007851075544444000700c64031240014483c000c503010442040012603100e0134940d8480f60203260420041d20b0402001800044091109507007080c800141d5071040310620189000800202c9001c10001c01098a0b240d00000c80540e100d100352420f0000000a4100800301e0241c001200c0c0c2080d44007030303900a000410001001414040c0450519209660700c86601c07292a40c5c3c00740500404114005640c55020710034032010f0302003203901090000c82520000d1145c0031760301015081112224910500100412900500c40c8001d101131703004142d140c4c40a4204159100c03d00082c06130384020040711507080c422604265001e0b00c80e541880055000d1189 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 894684316 1250 894683066 894683081
    0x12040507210b0907050d061a0a120c17120315030a0c15021218040e01060b1b0708100c1707021f0209060a03090c0806042d15020d06051302040602070f18 67
    0xd00740364075086400d2503d482c61240c000c1c0c6017100c03d07071401500d00c1c40d0bd4046140c40754000c0100420080c083c0360701e01ca0210702c2c03100c00d10f02c103176a864594403070f402100714204820485540c1072060f010510104179130304101d407040f00c1813055030200540d071458050f82c454610100c4200360348000c000c5414000c0050004003a0303c1405070000807807d40300d43c011400c40c1d541e5000307001070b5100855030103090021042411010140c0001170000c2d5403500d00003903078540812003904040c0c1c1e1107801c01d982c01c038450785000b0342500f401c6030309034000e0074030030401394441c041207d07a140c040080c0d015100c0559800d000b1079001010140601d4079185083c1c400310010809220b0031514801200400031b0b5864082003440c1c0954041d400c810080c800000c03907620103130802104044035894288102c00403902d80e6000c50282200300380c026030f45036915841d170002005590006517002d52003002500801c17916601400c00d45011b6001c5400403900d580300340801950318450240c02303000c85104204041c19942224a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 894685566 1250 894684316 894684341
    0x50601051204120c150b10020706020a030e0d060c11100c0801030b0601031b050c100b0d1709030102041404050f04020a06030c05043b06010512040507210b0907050d06 73
    0x4861013810342d00d81c0e446800a039009200381e80c49101c00620380c030300341e142c0101c201c125000a00e2480e2604101a4413401004006002d1160f1410340c81400e8071401c4081e0501680424108080200d01c00c014000c2b400c40990f507404c52007114a0026011464828801052132940301c00381310780e00e541d1380e03060702180c0201103e041544500b0005031049030305c1615440002d00b5221240c4810100741040d02d03120929452065080c10102c4a484584606004184103600703c039061000d402488811601c600c21100c50365010f40c0300050000340b010103601c0f850160b41e000c07902480982c031014039034882c840d41500c2c041e5000d03a5130403040010714020344c02840c0303441c02070a00b1424560f898407824030754242113074162140c00c80b8003085100001440515640d840131901302c0c10141c280306000070070318021f8100c2c00c3c40c004c29110100d0244401041030400500c50500d04003031400700d680301585103403107a20007100c1c40120a4085100e07040045421000d648028000700200c0e2030548500c00a000b10f01e0041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 894686816 1250 894685566 894685577
    0x501080c0d060230060a0f060804051e0d170402010e01050a020a020904080a110d09330314070c050a32071a041a072901030605060105120412 62
    0x260000a8040c4c0503492111070080481c0b40e0880114501c00d284000e0405208150f103003000d100420910042c4402d507501460b142c49960344602c0c4c146d161089018105021603407000744451808000508241b4034402c2e07945203c441e181440700b480d50028251402408544051001d4141e544160060020b20301680704a0305144004c0c1c0200d03451840940d416918031000162a414142e000007120094090701d00007060300390703200b01c00104100c1160180c640e12400d405125074401c2c10890a00d002e240350301c404055413201da58070180003801d001384415911640000014045402000c0c0240c3c180c0c1c000c0050142c1911603a1011445403075100e10203c00c3c111900a4425031041b92580ca404861410003400d003141884042d101400004801785030510013048103014012400350003441407a4282e816030340300e040070701d04124803c00030100c101c565104042c50354a94003c0040040c100da001e0401080503440f800c2c0116070b184035446a6040003848076000c0742c0000d8840b01c403036101c000c071807408 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 894688066 1250 894686816 894686827
    0x5030a0c1b080303070305240f12010203090610080f25030b1503010e2b020f0a080403150c05030402130605040e1b0105090a0303030b0402090d12120501080c0d0602 72
    0x405440c8054010070b40541c030110030040000c0d014442d041c0c11074001e0786480c040003c50314104040c5901340b10024041d0300440410300280d01c481506075141000240250b40700d291034044d4564601d42207642084000002d0000502d03450b011035620303006400203014048101c422010402001c0b40490940203444004900002052140491900565030707050244290601d00c0308060a54211030381611054000104140303a04200c1ea200144140c1c00d09107024080d0001070042c1d04088502103402400e01821a900f400c0041b81e03801272017500c0c4035060791070814102560700c03000c490080c1802d8002c50000c00118015141544815181018458007c2001c0c0d0710b400100d4142c0e48074410ad040113a20201d03c580c0100c03140111183e440b803080c40c0580c14503505000003520341020380b0028043c59526011038606469079012603d01d480701a005032800301d4035182070a902007840705400c00003506282400a845c0301d6000300c60480d100d160040001a64034000c0000101e0141402c50b90b0580c00c005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 894689316 1250 894688066 894688103
    0x5040b130302061611040e070e0408040e01081e0309060409020903010f0c09050406050d0b0402120724081302011d0102030d0906050405061f1203050c0601150f0c05030a0c 75
    0x6000c07255500e45132110720344991800015003180403c51510650600e03c280c40a0140000c0d101c040b00c2d40e01c03400d5410340d100c03420101d24500c107640000c04000082c100200da0a500010030705402401c000c05e032000092001405070312030090308503480c3e0018042000300607018031f64000c2c0503070480c018000241c00260000c1c220440708070603040390225041c0b4001700103900c0e107485440300400f41071312145950b04080d0303500c0c50305030f400034030091041150503920300c0010401c11484024001e00d9400e00c81340c102d00b00610680e0f4840e515504009842c1d00000380003000b100302c40340747e5140d040e1141c1c034610f1054264280a4121101051304502c014008256005628081c0e41c1040d4005c43d000a51410305040440c140300e801001c401c0b0016039901c02480030a521200daa080701e480c14450f020040c401e150403203052190b246c00c0038051107118004104d000386103104040704481521000102481064292100b120301030000c0c240750802c1c0509032020b4000c040d08400340d44a40c0c0c010344020200e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 894690566 1250 894689316 894689329
    0x3041203080a0219080108010f05060609220501180501051f050f1c091101180e130203060a0c021b010c060218030d090603050709030b1308090d050a020a0905010605040b130302 77
    0x480131000541210040182030300a1050180c800b00e2402d0a100514001021502074400d07040202d002e00454012802d20007105025144a10390703041c002e1280307580d0350450390180300141c10001c5d51103281400015462500c2031028032003101d9803507004002800300105540c0e0790452403202c2c0405c001004500121841000004c54044590000042c01002d9041c01d10404046202e02c9060003400210303c60184840181541117901c011440b001564031030b450a268000003000003905446038500b408201e5069401542a4440944c2150350b00802c0075200100c190040b071b4201e010403600c100001c0402d00c541c005010f0007171080304040d543d10360f050100346018a803825482c0080c502000a11003594140145a000740080c648101981d055490319200c04001601ca82c211102100800081041810640d0010072004046541405540c2801c0f510b800800100b248241210540413420484500c1580e05803200742d6a0141040c1c200018203269500140080311080c1c00000300100599844 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 894691816 1250 894690566 894690607
    0x1030507180f0f0b120c0a0903170c010b04061419050604060c050706050f042114070e060301053309011409070903080936090f03041203080a02 63
    0x42c54520301a4501182946803280302d070082100780c00c0c100880c081c01c0300380c81130041d08031400003201941c41064031010f035082c002523400100801c01c0c0803095002c154400d80a4001500150004e00a48110b03100b0001207032564000e04050030000b00c0c02c0c42c52801d140e401d000180943d064019405500d50000840c80d41050f405400050403a609010400100703201a1000340f1040c00e041d0b081021505c540301a90050f402503006d04040d814040401c20300381c12010300104c0d0880300e604c0001110005c11341c0c440000e030241c0b00d900307039042001c00c2d041c0c1014400d140c07046103d034a407980035500d01d80c4045088540042e0601048041144000d080e646048013503008001d071204072505030b0584010300150b80c00c0101994180694520100041254142110041c0804440c1826820112282c01c00d07191b01483c3c0c0501480c3c3c0c10f6003105c0743c915014820900904140301140d4509007075210481e50381c4614080e1002040d069956080003070f020381c2c0746580101d8410405030600007811028010144003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 894693066 1250 894691816 894691829
    0x3e16080318010923010b130606030b0102150105090c040914040303111c0213091d1912050d0e0f06010e0717011e0e010605071a090a020103050718 64
    0x42445004107841400384071800c0c0c03038002886400b601d9110310810541e000e030441014030a841c6040d605180a6004007080040201744201e000b04040914000f05214050750011a2401d201c64090350300001d4482c40751420042c3c1203c80383e090205008000d0006025694100018403010a040b201c600075600c161480040c814180d2400d414000c007074034403d15800e1070b00d150400404802c2c140141480c0560071800d03501580c0c4401506202c1d0b0b208065034419071315946045002049002e01c0e82592043ca801201168100c6055000b4103038880c07080d002c01001c0703c1c4044401c042490140c00076090203480c45400140c1c0c1c842c80a0312508100300c008444c00e80350440c0700180300c680c440b02e00d241c4c0c001b0030386c0c40d228903c0381501c244031745a481c0c10b008280800240f0103041c1002010b840c2d445000c1e151308002040d503565140e0001d41035030460711040350100000c0c1c0344442205400c86031144550424001400138420743d13001035004100280208003041104003c0d01300081020400c00000c115 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 894694316 1250 894693066 894693083
    0xc130b150c240f010501030e1506030c0d08070c0f080714060f03250e03190804030c170f1203010504020a090312091d0603120309010e010f0c02013e16 66
    0x3d000314018000c1005810070360605180001c2c00070074800000e9044541c1d140c041d804a12a15601c00007460312900e214007a40c03101d4200c1e0b5001c1009181230141c4252841405034444454070780c1c40c01c40c004a218015a01158080641000804090300d109004c4400c05060507151035190803c00c1042e500880340a40e80034000106960100d01d10f00e00c40070146034602c0c040201459500003e80c468106101d66402131911004040610001400316001140e002804204050341c0705a2110324180212540780c0c68094000440a12100032940c186040306141c2131030728603800d040800c0025000500450f007004440800400060540201d68250080503285e041c2d5181c17501c0c4104044041002d240309840088109000f001d4034000340d02c0005000d00c00d401512550f40e5140240104002c80301d6004640c203000c85803202200303e9000c1ca090700c240e907000384008140300d01d062480134804107540c0b000111380940d40401582c3c2c110064110104495071515101ca022130318546015100c0b0181d40001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 894695566 1250 894694316 894694321
    0x1522050d06091e02011d010509062116140309010902040606031a040920370801090507090f09050f150603060412080703020d05090c130b150c24 63
    0x942c10000401420f0440010540350601ea00003041001c0301e440c01c00c242156a41d085500c0c1c3c0c020343c00e503020070001a040340e0b1902011060500640b103994040b00e942d00044022950302002030303a00401e60754072500c84803000c81d15400d03c900030303500c01021020035560715000000141e40ba40074882c01000160303800701380c0000f00140d5030010076007920400d104520740b041d1980010400410505249100d800c82143c800c864404640d04210304014950100c03ca000b0305801002c1003415000d00c500300354207503504242c07640c204508a0750000c1e00030b0410340c81440108064095030f00f1207900401c40d8000480c0d14441c07940c61610780b0294505203855034210035400c0c05035003112020305a025100310000d10681c14a51500600d07013990007070001c20841e030840055869400f0783c045403056400c7e604100010f107000c4c48956260070048105500c030f0000f083c04281c0c0b00d45240541803544030000c0421144100320440407265034081000030000b8003840301812034003030f90312504079281c040345819850302d032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 894696816 1250 894695566 894695573
    0x51903060b0c210901140c011515020601052718010606120506030313035001051506130b03090703060f02040f060e040f0204170c1522050d0609 63
    0x4550f1214285819401808140007030780e07104034844481509445151780d00c180001d95030f0f014100300803061501c0317a0340c3d400c0080c080b00406034036120659aa403d541716640c8800400c121610810f0382a82401e0a02c20b4495804509680081e04441984004041c180401c00506c0c00c0d50865805480407481d16840002125200d0055650008080740503614000c0d90300c4050460252600019008181001501042c00003a41056415414030000d003040d0703000c120800425203456103000c0d00c02c080303070284207484c26805008090003501451403000c4120798080502240d9041800c0091081404810000310254070710015030042d1038050181800c2c50641c1000001c0d60140560100803c1c0304000410040c030010066000390b510301e05e04040c0d040c0150001038058104450906003c500c001000210700340381020342e039040c441602c00c0d00c0140c2c00742002c0010449207800c010580d15000c01c602e60400c00c0c800b171605403240c80207a080e66140d0312800451800c0024482c100c415960310720502060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 894698066 1250 894696816 894696853
    0x60915010f1203050c0a02060d0c02011a031b0f100908060f011521110901030b03060c040905060a12050c01090e1902090604030f0f0605090d051903060b0c 68
    0x1d0500072804240c00740c0740070480042c20b801402d014080120108902006403010701104280790b800626017520703030000800c4040181020704500016600c1c00600141030700c3c64000950a400004001d880320440204441b0300070480b050045a05c104540396980e01a0780e44c4452a03595007070356071003032101801c0c0780d111458070390302900c40314101202d80010066105c041003401d10454203890045406800f04900c188400140034007001900c0c2003003010380404451310301030480a0400da0781408110401c41c01d1507102c61090b69046424032081100b0f0000441c503811807500640c0c040e01c84450555034140d5041010101082100c3c5a04aa00f02c1001c542e031000c10a030152800044c91021030405c1c1d80c01800103221040d468803010740220b00c5d84620342c0c546060b200196000341c1011440300207032a01500d2401d58550444245107404049038405100107441c0b0203044198549601e04003000b00000d840440300518a010561205004a080190716004c0e10b81d014100000313108104614025120 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 894699316 1250 894698066 894698069
    0x10207030e0306090c150403051e011d0709051b07082208060601270915080a1a0415180317060f0d051606020a0c0b0412021309020306091501 62
    0x110754441028400d00080100701c1e402d04a100312121b00c80207180c8003008120740290760029005005000e078103209401e05a410b28a00768480d4001c001014809075064411f000014080c011644164000c2c007c800b042c0e4012a00912024058060b144c0d822214154075803156208869059021980300c124410001c104415000307440d4a050001d810402081d5035040010591410031848400e40300e0a0b00311003e5003584450b41c9580e080b030440c1c031541000043c110390014035550382c0a40078006012030021859a00131507002204012a01640c525000d8191000d80300307a4100156064010341100f00380301d030a86c0c4c000044221000c920796400c015100e00036038488134080d01c4045003044425513800354031400745003080342c42d200201410309103075180000d03070111840186074289000c41c9032500001e032003115907c40c0042100340c40e29048075800c280114410703544003078141c0e0031490061404c101010020050f82d43d0000740c2d8882c5400103468182d00b603e2420385600208004115140350b28003007030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 894700566 1250 894699316 894699319
    0x3090c15120c03010b0d093806090423011e09022805101e090503120c03090607030e0d08030105031e03031f0e0103150b0102011a060c0102040b0c010207030e 69
    0x10304640c50040c3e514203c0c414006c03003a1005035504980c0b0100a10841a20081040354101102e42800008592007504640d0807081e05490250001442e07481d22100440c803a82c4c0c004030b8110340204210b10358103900d040c0c1328100c9d229526050782c00115010841040c01c00c5949580100796040b441c0180500e640c0905140e120f98020b00700f608281603034000301402140e000f80c54518250105800845984070b0814a0348083c1f40401c004601444d4000d542d07100380c1d50201d0941703200064810b101800c6104000d048440e0341c0090100c451140360000142004500909000f00c00803c44800a02e802000710342c00c441c8940c0102c0103021030b040400c8403540c1040e1001d002400014140e80c400e540c0d0000a10800b02028503ca003000c00190500c0128002c009462195030315503142d01d0314800c6401f011149101240c906890041c95600c14003030000c080e41e0484080b002103003808140701d200e0b8403041c4500e040790f40800c0005031041032580208261242c40000580300c4440785030081001c03c0355200342e03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 894701816 1250 894700566 894700591
    0xc15390d120c020a02030606060a2106060e0612130305070501021204060b0609030303010e180307080a020c011b1419050309030c030303070918110705010c11031e03090c1512 76
    0x20340040c6c0780000c0d01900090122292500c414a07400c08845003000c040b10002d05401c81b0800d01c495117680c1e081030042d00e0302a1508540c11a402d8103000305406214443c0740000011004070b0b50f403c14103540c85041038041d00d0150300e441c005441c0e007800e9074000d00c142d20f501c1807200c081009201d128458903041c0b000880305503240c69111030000c4c1ea0f901060140441288030440440d04a00701c6130241d02c0f01031450400d5a4444065041103007160f0440c42c0000c0c05800348044e0145070350320a40c511400d2000342c12000c01d40840c0341d114441d4410401015801c984124a4108035081c1081d50050040340304400271aa03480e1008203250408043c1d0f45501e000c0c1c1e00600034400c4281d0440c03a0102502c40d0341082d00c007003110700e081143c003a10401d40883c1c0002e8000480c0b00501406400c40c1000810750707101c44110020410485650f80b0404507144c440c03105141c2a0714884448400854110691604607402c1070740960006490f5401d02c004105d0807140050700505204494007215031103400351182 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 894703066 1250 894701816 894701833
    0x90605040602031b10060e0403080f010509010603020a020a022101061d18160b031609140f0f0a0b0c0d0305010303020a0b0718080c15390d120c02 64
    0x1e5a203000c1d43c980704d0f8100060283c2070811070403c0080414602052105018141c1e07250780c4007041c0b600a0300e06500003103502000641014058114a0490b02c02a000d040180e10700303e0700314029044941c14a04502840441d030f1301580d9100040c011615025003204003904400e40b0185c211130300e83e8003803441410385103910104400c8070862a54810600e12005011003a0388811504100d4030541c0c0c02180715601401203184000c0c50080d500c04e40003501d4810865245e0703202aa04c040d0544291084d00000000c00710300c1c1d007070103003504107103c0c005414500b41001602c002184100c1d1500120b243c2c0801103610780003840204502c0c840c0c140541010446035046440094450700e6490000c2c140503800030100c1c0318644a035140d6211081e1044860702e001c0c0c1c56084543e1181260221180706841c841c41281149806100f1101d042130700c0710b0b034260050914013800b070204004900505092065007600d8080030010b0000f5810400203030b0300c0103e400d051040c01011100c10405d641c3c01c55001248 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 894704316 1250 894703066 894703079
    0x60a0e010b0d03140408012919141302120406180c030206030c0c0115060311091c060204170f070f06052a0a030507050c1f0c05030d0501080a020109060504 68
    0x1180d01540390589841914042400109000c5109079440b001d2198a480015050071076110391803000101d141400e9a800700e000c238104060440007040c2d031800302140300030401102d0318295441c00c10440c00382c13500c40c1c5989420000303000c9800a22980b0080c00700e240070001048294400d11403440b40041450b610b4803030545403a051b120031400002e0060400001099006c000030040e03803000b014001c005e0250314030030740f5008580d02c140d1081101080c10036000810a03080c69058a543e80400ba02740b82c1c0c428400c0040700715041c4445e00a582d4203500300000300790764116446051004041c000100040010840300600e80829a0b02c18a140c200100e002d001c696801001c8a0b1401c3d100303841c1c0032441c50407040e020a00207011007070320701502c514002d9104068100c0041e200c80ca0048055803080c80c00c00c803d11190040780d0b0003880a10f5403460030010305d54042d480385081d45004004490403d5000081176049034001e81000704254420b4051500315a480221400540003e240607801d003840d055 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 894705566 1250 894704316 894704329
    0xf1d1606030c05040905010b07051203091b0a0936020f06090103060b1603080603030a0504030f08040914090c0301090b13020607050307030509030601060203120115170702060a0e010b 80
    0x1480c0406454901d4058060300c200c0955010b000350480400003540d48600e03811499103c13450840b440d000c2c115018a03540e1140c400d403885040024090311038010641d014104000180326029800901e1600201d0800c00d01e220b011544142c0002c2114100c01e442c408259826003a604a240c4003000f440b144010785031003140c10b540003c160707540c80c2c403040048010b80103840160444030341d005020805a0b181480d00843c50020341c003a403203c01558840f0001d241e12445907048a501182d0100030400c001149540c00f2150b042c02000640c3c1415140d07403e807030139120a20040e986001600d0144468994103000c2904000000c0b0000c06c20862165100d441081d0024100c6450745c2d072010940e400d540300c600c101c8040c1507000701980d645140a1178050400d812140640d4002c4c4218000400c13903c0c000012103c5010300c140c2e0204076a8a015107180b145810a0703081b40030000e5400640030040035140104d4000c6030b5030f0b00034024500e4805010802c80700602008031103607040c07807a55281521100d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 894706816 1250 894705566 894705569
    0x1203090307121109150f04061401050307021c0906080a0c0c06050c07020402030a020c010b011403160c020414010509241e0603040b070e01050705060f190f1d16 70
    0x1c44030981410392034188200c010410090702d54000b00d84004110b0003850070100c010840d501180e10710504480b4031b0610040b0340d0300303000e60308540503420f1032060b1351740c040c00145a02c01b64034811036521191061091540c1009020401e011400c0b00303005006440c0c01110140e40314420032801c009102a80c1c50003401c203443c44002a1919035528080707034900070b00c5012201902c0d00070344259582e0604280440081d800401540015442c200105203250301c83d0281c82c1d03140303a400c00402e045444c1c200c420101750328aa86200e0501c00b4400520006171518040d00c0e10003030004400c0c40242d850003040c8541c0c03034001030100c2d6100103c0007207080b0611044940e401c02107000c1d1180820244003800c1e0b02001401c28814a5010350007004000c1080780126185120320300c0c0f65140c003d91480c010054030f05004158004001e600003d001800908180a90070390140440c13188503c0241004c51204c101c5a484000001c4d090b140d01b045c0701441102c1c4c21181c008607403c4010b084690070a40d0848001440c6d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 894708066 1250 894706816 894706829
    0xc03070f1707030e09070c12080a090b011203030c180608041a0412030b2706031e1e0316031404030203010f020705010f05101208070507141203090307 66
    0x140e4108000784604441214410700c505180140d68988a04000c1c0110300301401c4d079481550f004c17000501303252140c4029104039522106d1004887d20181094645183c020701504100e640c4661840c00304000420550003071420b2134031550071461600b230040a54461407000c1c42440550710403114a101c0c01418401110481d00d0f0080f5640c9403464100a16048403a00d900447c500605101c14801213070101681414562070800652820200b400884484550403507141c0310541003500720b1501d03810000d41d00c004002e0607260389000030008082300c000304010302011540100c2c24454103060b46417940030001586802076092581c1c1070340107809540888001410001c91500d0300781540ea05509690155500800078000c9001015000c4029002080b040d079440d0f0800b10041c100300306500c82c060027802c60048516030307242801341942c003220b6078140480318240204801400703d0014000000941542d14a010508400d6002c100542c2c902000c2c01b10710b13400400100c807031641c0010f440001c0314034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 894709316 1250 894708066 894708083
    0x30105010e010b13083702010504050904080c0a0c05010e010206190b1201060308031506031003030f0c080310030b1605030a05040f06050426120c07080c0f0a0c09020c0307 75
    0x2071410360726200070500d90105c082c40c03280d8650b8480070303800d11120100c5079110012411307500f015600b852075000015140a800714604110510413410a00005940240104213161501c01403210491a02910113030544030300080718018002980d10112440404ae0240700400090410710240c0720041001c840141c01c10f03503600030310b03100c0740c07200008054840c0800d0002c000641d0340782014030301940304840c00c1275941e80044240e81c140ca0060140c038011264500400d0005003940e074140d80400603121904c007440404400d5000240c1980d000b5442401000307403880c0340c2c92452034401c5500714041c00403003070107000e581e48400d2298070600341c80c1e014000d0314011890781c449040c0b20450f032a07080e90140405090804000502507510842d0002c0d072404400d2045040d110500c50b0b035030703005124075402c040303e0315000b00700c3c0200180c01902d44d26004d40b203c5803501c031200d90b0443c80c0c480e040c0701ea1900da40104d500d01050082c03500502c0003c0c42042e03810361810b10340e8216141c81e44102c04004101c2c4a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 894710566 1250 894709316 894709327
    0xc070c15031b36050306010f081e0d080a060902040305030d0f0c050315060d02030f0907090615140f0313110f010c080a20010608070b0703050a23180f030105010e010b 73
    0x1076148910011301024007550f401d941c451910103140101d40c001c174115407150480300d0341d0b42003424102d03603020350300030000d03001000d03060800315070040014004034030f01d5448260100b003088146c40108000c0d0703c620011681e440080250100380c905400820740b039603140c502842003464001049940c00f400d105c010038510b40011001030b503540074003100c4259a510102c100b00741c0c0890351080b00d001e000c4110403981c007990380b00200c00c240c62503409600c4d60782510301d224040780d03030140c2010b0194a170000c8005003051680900003405405c200e6020802d10034107a003040900100c100001d01503a015a1428820454140064600400740c10028403070b0000049049506110b046144003107800402c0d80200d41c0c001d01080342c0a0702d16030081480900545000242c1d041180c01120710280e45a1581801c004483d0307005c1d1401000a5a00311003000d0a40300b41c1c0342c000340c1000070080c0c20f180400d90022022030343e0511096041c00294180030360b2501c4014415814040001c03811160300d00340e510f5641c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 894711816 1250 894710566 894710657
    0x1d1018080601050f06030c121806090c031c020109021c1703061e1906110705090405070905040813080a0b1f0e0603010b0a0f0e0903120c070c15031b 65
    0x234440c3ca211221001e07000e41c1402071222070079208100c00030717007041198090740301c02802d02d4560034005641030707055005258400c1d8a0540c0e04d10441c042d0040d00000800c50400e8001c140089041103400e000c1c000d84400c8003040000800c514200310030f81500d26401c5241c0a004118030701c40c0d074943d0490281e00c506107204295503c03401a41409003080102543e00d0b9503d0b4040c02d00044502d100c00c0c54080c0d05c0001c0b6090a008207031030b1046800c4001840c4082c606030051004000140c000e03220b03c40200f11854100000d058903200a0081c82c00078034000741542050b148100e000f8250a041a241d01604205080240700b000140c64140000c610a030b19030f03500190041c81310404641e089400e60000050004169602008484048190700c61070303500d44c2c4099072244601928404101190340120390421115000303404402d114103580440300b80c0340c407030265607151f400b504c07000000c1e04c0e84054035100208541d18001e030300a90030b0510355410452a0204041140006600c0754260320f0704200c2d10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 894713066 1250 894711816 894711841
    0x15050f04060513090e1b01050a0903020f0607142a030d18091103041202010507170403021f05190204060207060302090a050909161d04031d1018080601050f0603 70
    0x80150010400203820f00210b10b50306d51441d010a8420702d0352900030361109500036011505045115526481d129045038200041d04004c4000180c004005100e1030340050407024811159000c10b00043c1400b50315540d000d1400d1860600d1042050740b062044101900e00244c0b291040c9810b040c01d04510b400c8500d004c44002180d800b200d149810002c0151405142c00f0007140910f00580c03c90311220031390f640580c2030719803e854072000598084114480030315a2450b00d600103100c0c0c8140e81541951200311a814550b041d418030185507200140002e91846e1206844a0344180106600b080c0c46e1240180d11071002e8030902d000c0c141c000401005039500c0c10903400103000014500c0c400e50074402c080030740d603084080a1030542040d40401188404590002070918100d0f4070907407899640f03680d0121140c101280364103000301c2142c0b800c10320359603c0f481d40c80010544c40d0b80b0301010b03001c114804651074807690b000c0c0c401600b2500050095480d600c2060a0000f010f0f110280d40351500c103101d062 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 894714316 1250 894713066 894713069
    0x80c1804110d0b0603010312081e04110f040c0504051e04050103050105071b0c050f010309060608030a090e01120809030304030605010f05040b1e2403090715050f04060513 75
    0x24414904860340c818414010082c04203000c1005041050710710803030038000140301c02e010242031401089011810584503d03806980401005000201c07080c0032090408604020b41c0d007180c1081418008042605002001c0c000340b450454003403144034951a4007034101e2049001d83c034003503283d0302d100f40881c820803a59200100406402003001e50303541e04145000b008c081c0c64880c0007401e184070070745095500c0103605603510741040345620711031b18100800401100c0301084034141a1100440e20103e60b00703124103402804084055540c0c0d00e10000001d010b201c0941001101ca41244014000c43d0703d1000c11980706a80320a4203503852032038000003480c501899000078985810320002250312440585554122101a1070074000003007564100100410401d41e07442c0100074414034802d0078a84000f80c8000c508840e12400f010091120340385003181d00c11038582c0324503405450b04222403054880c8040c00ba60051400c1400c0000b10500c110480c071403031080700c0400402041191000301d04805500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 894715566 1250 894714316 894714319
    0x1008070e1201050f011a03010b030a0906020d0e1006060819060e13120c020f0405190603060207120e010219030e1c0c0b041206020705100c02030304051903080c18 71
    0x684410940a0700c0d018000c00c0381d05a080714041000041c05241820210010300c0320007041508503030a101c100422504010b0840120540742c80c040e00104540e0b01c000e1100b0341d81070310080f42059004004502e0b00040f00d41420159250540400c4802d41c0040c90700e80059881c0d01800e451008000c2500141c800c071740104101f81008824400f60f09010843c160015208803c030781c0618101150035101c41102d040c002c1d4100003c85005c12040c50b1541c84158446104685c01c2203100c204104081102c0380d0707400c12184a0340c001200400d00000251001c5001c56078034040d00d8500103480001d4440c00380a110f100598a0040a40201800b80170140800517020b003500d0f000d41400c500b41c0c82601c942400075288000002d00106139103540300211407c0e288584416015120031b030b55540000d40c0008020f9985006804d0355101a255a0007410888049540110749904040c18160700f441840c1a01012008050f901c1c1c03c0000d8000036490b910a4090b00142d4850610712600241c0b001c40d140c3c040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 894716816 1250 894715566 894715579
    0x304050d1b06021608030a0807180812090108010e01050307031b0302100e13050f0c0a02010b06040303051e0306010e0405062101200306060d090f0b0c04060f0c021008070e 75
    0xc0340302d980c00240340c181600c641048040c125036401e10651a48941c3c2d00b000b001607000d90000310035078081d01500b107401c2590310344414456654110103040010701300c0000b844410024903e0035540c0d016103028090030641c01a00c486500d8000002e9030390840b403000400016500c2403030103501d08030701103400045401420b14074200c90162002410803a00445013442444140107810102c0007a202e69441545140300c2701d0040d4a43c0b07d00b010f019000038120074115074071000300e50b045456603c0600f0056109440b02d9448035405580119000100c11703960304800c4091007000490380e4001e001d0f1000c030405640000361038580704080750320744003e07070100c07490060300c84040c0300403d8055104055846018416405110340108406d4003880117071030b07030b66101c1d8042c01601c00300007244d440b03035600034400d00d044003000846668001c0b244d18102c41c1d02507a10408034007000000d41200c15080000c12510700320700d00d6182603002400c013000e45902801080850000100030038006c0c800c80c612040e005205 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 894718066 1250 894716816 894716819
    0x50c031006110a021c060f0b0913030c0809120106090902010314100e15090f090f07080c060309150115030f11070b0604110f22030b01091503080c1b0a080304050d1b 72
    0x501d02400c942c23002e0034016480000015134030140c406400d5001303589a950302a6110007500c0f901c529810641e4001c1c0e20840400904044110900c1031a009158601c00404e00228900000d0211900759031640d00002a40081014074081c80841c00c05507003080e4542c41054554111a60078070403001e030350503040191802800510200d00311124490340345001100d04c0040022840380d2500c8591043d40d00c0303a885500340c0d1940e4944003000d982c1c0039840c00105c8107400343e0a030000c82d1200302071384070300b4800d001c500c1e10071101035040c025200b0801d0181d500740211403804005030b1652050510140030303801694042180c90342d07160001c00e00059840c0c810740d00d520540a01031507030b9200241c84500c0c1e407182d0b004015001c28072209a0100c1c3e4124441d0400da81c640454000500303c00d41103d0f03080151040040300040c01100905241c21408006010000c904280d0880340c00b0103038101c0e0310490016200300010000001110150756007910403820240c4503107480c0f040c901040f0300e12803044140450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 894719316 1250 894718066 894718091
    0x60c051222140a061b050a0f030206010602061005010c02010c0206040b040f05041b050c0f0601410f040f0216232e050c031006110a021c06 61
    0x180884440050110006226992040b4202d8094181e0166400005100080048601074150502c80701c418496030102410765580b07041c01e000d803102c070845500042241d071b1014180c0c1009003074050680f81c00202446d0800842000080c00207105142c10400400100402c591284c10007400032503024010985940d00c0c0e01c59000c0c82d0300325008580011030020000501c0e40341a02541031a0120b4942d0f09202d036000341c00c100c850391300a0105441d00c3c130692180c403452402c1041018001c288101000a0301809030200e0310aa6445000484600340c00781000425034040d003030000c5030240201c46400c1680f040d00c010402405554210131811880400c00488000300035160320002d84c402c90002c100c2c42003110b4a41802500494181590303071128010b10600d240c12009a034a003406d024550003401802c0c0c0e0340105560b4101c9051480e01d03400700500ca09145020185000340007103080c0f6841811402e12050340d100032b5408060b204001d103c002c004120b003141070001728590007800074050212003c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 894720566 1250 894719316 894719347
    0x4121e051908041e020d0c0905061201050609060123031503060702031c0207111903030914011e11150919050613020102031c1d0102030c04060c0512 65
    0x40c400c0310980024036250000d030300c9800c00b58822a407001c0da4110859009502c1000001c00d500102d800034411044100442d80750a07601c1c0051110b0030020855140010601103190040792806115a05042c240b100781e9440801d503a51201b02032800c62000d0300f00f102074144282066050a42d034410000c00e01180f44041c6103c5600703040107900301c860b6a04e0b20002240e6900c548041d0301410080304041091962450300200329075805a112080003c0594000a95104260320b213500ca550b24070904004140d00454048020854051000c43c03181010002900314580710600d070b0303540d5100c00c200d44003040c0900c400c0b04d40c5200761003c5403078a41d80035551856140d8185d48802c0c4500c1551035000e82404140e4220100d140d102c005040241c440d640b030300000c0c483d1404128194042401800d61b45400c041e41514404a00c0001003a40c4040d8003000e24201c16001201e00580d00400c108040d03001140211400c4817414544043c8110850400030b0070400001c4030880003200002d4581e4450302da54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 894721816 1250 894720566 894720577
    0x30809030d0915054c06050c070e070c0201110f07031217190b0a1a27010c140703061505040b01020d0e06090103111902061e04121e05 59
    0x2d2020401511140b0a96581d42e80210769401c0845a120000380611790350380c01c4050a4000b501038412020300400e00302e040740d810b41c106c440040c5003c100c49413060400c121400c010000702c41074490509041c0d1006010406080d4042c0c1804014452009468810450302701c50190480c25103081a803030f4070b800f8208030513820071040000c2c401450343c107103040804040d90040211400340e00303401000708007900c0907006515040d40e028250601c0010051260100341d01459120b8035490f0307441e00d12a400d0000c2c1c5440c0340c1a503410361220780c00c02605907040321a05804c1600702005c0c20703c201803000079502d1300b031040c0c03c001c10040c00d0910090304903d80c40640801c2c1c502c22a4240308041350700004903034401c219441400003407140d4070814030301e040100080c1701290041c54040359044212881d06413030b5002c200a00c4035040c818110525581d0b040c031805401601c9150751148008010b1071500c403172440608054140c4d41c03901c11041165001d00c056401c0030002ea8030400490000700c0300a041c51300318 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 894723066 1250 894721816 894721853
    0x204090b0123040501140d05070216090b06030a110714062415181c1a190c0507020904030c050705010309080f0d060f0b030a1104030807030809030d09 66
    0x204402c41800405070040409000e500c40103403814686020011155010010381410551a0030010354a40351010702a82d442500150010200301e001c4410211403c0107542c004a10503240c144903100a40d290740441ea00300d94041008101103010080c1d81c2da681c480c040005101c40a00300d0385049101001c640305100e0700341500414000852a07600380400d001e440560740d40500c0f80d4103056849950f0001602404d044800200308082e900004200c54007641e0801e10038403481384602e4800c00c010120780170000000307145d003404d840c2041c802d81440802900c10401c802500c0b4220140d910303205205842446030010118913850030181005441c0c1c0500386015039140c051548e000c95154064050181d90aa00c41c41c03a80c50300382c1c5240c1c964070a4200e02074041c038640d104c020015000e10b40380641e030090929450000e55a0400908000031030320541c5001c00215410700081000c60740a0051325080b9030517050804950380c95107480b9046100b01c83c2601106c0b444c0001c5082441484414180341094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 894724316 1250 894723066 894723077
    0x60506130b03030714190605040507120203150c0717030735060f150a1101111215030f0102220f0506070f05070e06010f0305010503061f05040204090b01 67
    0xe0960141050710320100800b41c150b0700401950000581100c506100b40500c40107071840c8103040d000d4203c41160030501a00d03910b860744280b0081c800c09000d5a0010417500078904d45600303c2c0d5010984462851000100380391f140400150010502c40c101c81480e54090500c40746000040030102030707500305403103040004402c8185481d0a0111030b411040715135201e0141d201c7c28181065412400000070447c81d04405500e4401390b140c0c0366501010b4204076158036854484c10780e03620091240c0d0084140b01c84980c1882d800c80305000501c800c8800a402107590181103a9070714a02d0940c410b00740c1e00140c0c040c400d100005035025030642c042d00403508606d0344c94500301a0880d00e40742c1c81d501d50040d40d0031000f02d0315041240c1c3c501240240320701d620400d6030b0381c481542602c60a0400e0b81c207078407080709440608204203440d07034810180685c030401402e080286506009c0840d0f07440e14014038282c118000d03d2084424824024a60300007040014015544c8a864400c070340040c00280e8010340c003049 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 894725566 1250 894724316 894724339
    0xc050709021315090311060d1404050303061f080f0604090203100b0112021207050304021f0e0a0501030905120c070314070905060307031e0f121107060e01080109020c070e04060506 79
    0x1845a142030003220740203c020f86da03814a0408000c5540c0c85017404480c0c02e50380310440d0448900c140d048071303c030740d0088001d1500c0340761507010701c840f18403134000c003071038980c1901a80480f4035040060300380c000030b035094280b61560343c14000c20020171547c280070b5072510890b4107094440076180c20003211400c0c20380e900c400d90850307904e160080c1e01a07030006903c19048500041c20140c444c0003d16441030008050707003440c03048408030980020304111214001001000c89000c0b90511100c2c200081c072081c60108088085520751580710b64070f0040c440001c0300000360f260b180c48130800401020b160407010355410b003c0390100c6140c0e5100544070386400c10b0300705400901030386008160f510459402c090584100720341d1040c1030020b8241000120396801844000c80041280110740307e80080c0e1710307140c441c412600c4000440c039001302030b48108104a600300519050f039074401e6107a4119000c0d4503000d03803907894020105040c5034071f5402c800c8041164404210070301026420140c001c01007a1586000f1301e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 894726816 1250 894725566 894725609
    0x405060103061b050702090a02070803010f030b0f09061611160e01060c050a030804030309060f09020103050c160b270703120f050a0e0a0503100b030f0d0804030c0507090213 76
    0x1a0020600804c60070721211000d0300f0f06014185e0310440c095001841c0040d15642c003203640d0420380051043d40d0f0030303850500401101d000001e400818900c481115894a03659175540e40300018140706681c280203020f1602d0500a100b03030001030098030309940301e1913205102c04040304200c4c8207a6100d600020000114940036101c1c0034062500040680415091501c00ba60204009481181015601d086a40c04900300388103481070003c0c62f5a012074610a10300004003070f1b400140482041c250100083c9809800000a1000c080c0c6e0046401109a44d000b61110102d4924803104401c5120070440f550310600108440c020f4910a6118032400d24a412003102c0c00341b20f003030582d00420410003d01d500c2500920300182c401200500d08549a1340300c0c404a0b007041d100b8526429016100c0e0352540a5160900412410402d00d00c02000c0410340441700401604025101a05100007880d41c03d040c030800740086000751440c03203021f540d07440200e0480d05503281c0c1c41c4206502e0320030450051021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 894728066 1250 894726816 894726851
    0x1e0905010b0d0b160c0f0c26030405010c060207060f1b090303050a05160c030b100e04080304020f1f0e01082211040204090f0b030f0303091903030e06040506010306 72
    0x356070494030f0300c241d80d9100603210114000251100c81400b0802030380100040000c00c44020692290b000c0340c110070301d019805174403048140c15800920304842c402e0103070760381c0010a8400701d400c2440c1911200c80d860130300344000e11a00d94081c2100d42480c1508810030401d0b0401b944172031452210048642203010102d45026070303408014006582089440900d41c480e81c040c1c40c070842c1c82c614400300306034195a0510184000d0307108880010800c400c011081c8031018200c1c2c01030611200442003440c195a40804910004100a110300f8000c1d5044a0945a442010360388003240039041d4071103510450080d15034400900850b0001d04107200065070f203200307030020110660000c40f181030782c0d204980e94000200092031b011030700310754240000a01000d06001703a480c070040b10302c0005501804901814182001d40e084c52907d0340c13013002405081000021400c0c000b500725511003088184c580780c02c03009400c44542650051040c3c1e411302087c8100800e009048030f10030b242c20008804131040d04001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 894729316 1250 894728066 894728089
    0x30c17031602130f06060e010f021c181206050c2a0f030a030f06120b0714130303050901030506040608030403081810050a0305060a05060403020f03011e0905010b 71
    0x289030814080c4040d510000350380c40e080e00c0d02c000e040485014041d160501103800d01007034815055100c500c00c00810f03030080030140c00040d0a182003a02c8505c42480039603140719001c560505d95540940c02c4c8001c0d8030508200b450032000099210915548180e00c86800c0700c1034205450380c034a0b200201318126140c00c01c540c049007500c246d503515518880300000135540750303600c01c03155801610841404004180020b041c2c100d141e480018541042014501c21610070b501b0080411a2248141c404141800c4420783d2055035841c1071008441403a0340401c140c06a4100725520028078007001c410076400c14040c0030561000c0c5d0b8100090760321781c020042565014400e001c1d01d600700f0042880469200340044c00003c0d1180308030440700c0c6142010640d20002368051034001007021420074819545401426000002152414441802e03c00002d00d184240d2000074800d000c0601c1840c266282900003002540014443e05410a400725070940940307483c107802c9900b9484c2c40340701c01c1ca902d400c045051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 894730566 1250 894729316 894729359
    0x8070e0409240b033f12090c19180606050414190815010602010e03091c0f06061706090a060203060307150906031a01120506040b1306030c 61
    0x12070291661030041c03520107524007600401a165000401c0f1a1400c1056206292030000b000c00c400d0481111000050051a48406050b20380310004100140d240140d0f00741c1c0200100b9800c6507258040d08502d4a03000200e050b401414074a50341c0c0c0c14140140c3c4036412100143d20090171101036451590484003103002d4440440e0081c001441041c0201d20700708161203014091007030031188214034030403000c805d502ca48000d601041914242410042c600e0340144407500007031100c810b082e603046880b4010762551500441050742220408a10103c0c10030751540c00003220340510605003000f00241295000d1190625604031140300c1324400042c00e01e114103115006854804056915000a54406007101d94580300b150383c085407048400e044003038a0008e03600e4400d00d0502d80100034081d10300909206002901c2540e104503140d0b04242c45a1803100c0701e91001413075549080014000704211071030300c1d800240b1024203468000481d0310541c140d9002d00d0900c680155180302c15000302c0180300091 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 894731816 1250 894730566 894730583
    0x50607081302010c08031506030a02030a0c02070f05060a0507140f0c0a0f090209030111030708041505160c1b031104050130050c13050703060605030c040317090604030308070e0409 79
    0x40c404175802c0e10185811202800700b20020721034080000c0c0a5070400e8546446180e400014498040c520b4030407000800410b001414007946001610401089144a824003c210001c0c40c612040c2c0714000301c80d10030794041d4482602540c150460b55440201c2c0c45209000d1180c8171000100e403404044041c211005003e2041c0c12508180404010350001c8000503055900c0380e1154028034603071009984144910780c2c5043d2240740c00e0a00517095a041c16807908101d142406000c141c40d820061842d2400250521800000c0c0600c4c1480c10842100c5030080401c0b84d00d2001300803c00c0c0d94500c0c003400074040390b0600160340c88605841c0711021100480300d941d610112610b00c06200440328103a46801003043da2503144002001c02c40d2200d5080340701c4505640c810030001c42c19014401c410150007070703140140c01c40ca00742c0740c1e61034544a50b0002400c85000b42d4201055104a901101c024200150426031160f40d0307443d0103840e0642c10707101c580108103004040685030409204100b411500320b02030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 894733066 1250 894731816 894731837
    0x51909050c330903120a021605090f010902090a081b040524010f11070b071209030b0c0c160305030406110c010c0f030e1206010824010915030b0405060708130201 71
    0x1880c0c6500c40c80302144c16010b440002d01101c2040000f030140603800e42c000e04003c0f0525001c0410341811500114481c45080091100a00e04662101e05450101000698411240000500c034958035849800140700300c1d8000c004000c02040088001c220540d018480e684451030300b8580720180850311071325060340031005102503109200c17121640c2a00d0422103292250079210504020003034008080032440020850100203404ccd841d1b6400c04902c0c41c2c079100b00ca09560b2032040d90a1b0140c0200c40c1c403280420740c14143d070f9092185001d00c550482641e9001c540d40c4c80c155840350418401e010110700e819030b50310480394010401054014059441001004060380c41c100410300d035050640400c4401a1400c410791200c4051904a0311144020201985007008507440c14007482584c440740419000d10f00008890040e50307a0550740c520201140850300341784030350031b0380c02c080c1d002034421301a040902c802d00c10b010504601412072503940840fa596081c0315443c880360954002800603c21604 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 894734316 1250 894733066 894733159
    0x405010b1903050f0f06150a090f0512060f0c040b160c060f020d030515060304050a02131e0e030c060c030406050f0403020a031d121b0a0513051909050c 67
    0xb03c3c1e2229004282847c004011020841c154200000d100f0120300c42107020310228640000d60401000704170740b000c40c0c80210b5142c868442c00050082445190b0000106c5c520000990a4030064040301c1e80441e01c84058003050410f50345040e60684030420140004990b07141305108808212072140c00500204812402c114000c00c0c0040034090320540c0000d175050306968040055002d0b0b8000c0c001003a407032034907004004d844213003c022030031203d04d071005440780c1c5501a8102603442c40d0076140000ca00e074540e440c180c118440e1010f110128000d46040000c0007168070061400342c0d00800c1c003008a991846504003001d11300390380240c00b60740001055000244510400e0f043c0000703660000012904a00100c1c02da280341a00502154104205c0c2003a04184110704132690340007100d1003c002c1d4501008510400e01c0300c25401c0d84a51200c1c0000e4002103030399890018440c00d2582081000381905105490780d4050300546e124005881c0701c4a600c01060139a012200c0c103100003511103042d2883c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 894735566 1250 894734316 894734341
    0x40f1a04060c03180e041203051003020609030a020405180f03040308030f1b0301090c02060615090d060207020a140f122a270106090308030606180405010b1903050f 72
    0x320480400107000e50001c56030b5003610f81380c002428500c104480a050510b4983c80180c21440107504041c6818100b1060001010390340741200d805131b500e25590461000481e003041040728000e500702c0d0900050081c500304080e82c000ca0240081e058402419108a4880d1203100b00d01c0301820000044c40401d4020710b408600d550419489aa442d4400a609a0900041c1c10980c00a51016521412654815014000140e0041c012121448501c48402d4000079038010346426502401c3c0c4a4492010080103a04a4451030740040082c10070340e0382c1d030101ca403002196401d103d00031203030350400d1401c1c0d0803c40c0f074601c0300300801c60180c6110707641c00c142c08007401e036200d8001c521a20002c0c2c10315a26110230402030107240004001443d1080c5102c1c981c4048001a4402d4041041c00803003040854441c41c196034000400319002d03691040100700001058000b00d400300c0d4424903100000078071807034070f00007001e040741e00c581e844040010b0044246d0440702c0460740502d00c4142500040d60401d200e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 894736816 1250 894735566 894735587
    0x303011701020702040f0b0301061d01091d031305010906210203070905090c04060e090112060c0306170d02060c130510110304030c030519030e010305100b0708040f1a0406 75
    0x84001030800720700344c0000703040d01c4000c2601102c1541c0c50210700b40c0c6060a0040744c001c1d003032042d540c100341100040725590060341407181c0701300070f0380d07840b1011200040846032030f240306940412241c40d805900001c0800d0b6230780e44100d40c040303105010001031040c040d2403c0410744100c4d09488500e09600d11007031011758402000700c810469503107004074180d952002400c0c0a81043c607902c0e5255130400c5005408100844031481c4a682041d00401c1b2131102c05100f4410039030300c404085251102a5801e501400183d0040c414289016400707902c1c0800018409440c032400c0d900700c03182e548030308608106501c22a41c4481244149050034017003402d01e0000314040d8140342c54000140241004814150f07089a002154081400340c0100f050003c1042201047d01409518400c182125500648100b00400300d0314185619500026100000c0d007400c98004c02c0210304c0c01da40c865051400e901140d00c070307019640e0000c1440c50041032803203501c000c1c429840d05100105103060305100c0c003900c0c010380d00b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 894738066 1250 894736816 894736859
    0x8060427120908010c0c15020702031209150c0615150a080910140a0605090f04030c0c091b0306090c090522020d0903030513210c120203030108120c030301 68
    0x30000e0124024071481c01085906d50f200d02c1e50f01410324141c590025404000304104e4010b00c02180940c1c0d012448405807040c8030101540c50380e0313004c01b00300b550701211035141c400440031070003020f5101c4c003040e0315102d501d10b06640c0d110801c09008112041d45410340300304550009000000142d801800066040060300c411101d1150507020810f0541e4403503c04401d0ba54105010f04c29024480e001d50b0019000c201e4240001e454510812100d002000384040d04020452a2400600080f40c000c903016140d0020140400d11000c0c0506051440140c40540024a04100018031240da880741000318622551610855803800e07003041a0008606030a2018101c84c10030544000fa85200130b20320b0609c4041b000c51602c5060601074101c44005203404551000d00c0080d600140c00e0410100b0748800c00c44d018045001854400c0304c800d0480c8400170710601d114402015074940000185048410302000c85180120b003500d00d548c140608150060306a00501c01400040440c400c046403d100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 894739316 1250 894738066 894738077
    0x903030e0a0c050a09020301030803060d020f120d0f11211b1b12150a090506130210020f060c070602070813230904020609030a02100806042712 63
    0x8038051940e080c9168007100b2103020002010400450428824450041246180850440d85181c070340c110310707200c010400c0e4490407402002c0da0131583c59003420710403044050003003589403010018581c2c2d900d040088a40204903c417041d860468070415038205401e03180c801402d42609000b4560524450340701010241050922a500e240c0701c49460b0700b0780c1a1050740c01410100e40b0101203034040509624101d005010003901190422400075803040802c0004240074840d40c0c4042e80b00c401480e8900c001012801b4031028440e40500c07164902d004035008130b807010706c1803000c104140d0744c0313070000a0420042d80001c8009800c007481c0101a2800d0381c000d51001d843e01c1ca00765078402d0541d00c43d842265600c13000d00c0c01480b0165100340880404100c08900ba800d05c000b1303e0008807a84401080203108003400100c60116850502451040a038041c00c0f02030254a407030341c081c02c0518101c1d840c9018524104001c880b00c1c0d040390344076407100700e907608036140d101c0b04d0b4070390340c4151000c040c40409100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 894740566 1250 894739316 894739331
    0x2100b1210050a060e09031813020c0703020306011d0a15050d060510050f0d060902042307140901170912160219060219060b091504050a0c0e04090303 66
    0x803028040a61180040d010001d61403038030808400c00c0340c52070b4015511072980401003050126000084070310f507985420546c501d5546d0100050a031a02240e854003a2900201d00c160f0160070002e98103064038401c0301503e68903a242e08031034150140000ea620b40035001d001c045541e0f16010f601c0884941c00075564480301a03140d2000c03801c29000303003c00712805583e5000300460290020420400340c10704550180c1001408000124081e445a0015044a548041c0a021541c0f0f5922082004848201407e03400441e41c040407000300080320501c0114021a01d807082d4222004100d444c1d0541c143c5482c1007022002c0d120b00b070080d2005140c03c0c010300c13034075100c50740911450b00a031411500d045050390012005106001c0b00841d1014100150f090035503092003010340202c3d23412203040c10b20b511190458124101800500780031081a0b802c51001c4003441002c000d2551090190760041e80d091056031180c545000440d94890b5401002508401605489103016040740e002d260082c9408a40b19 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 894741816 1250 894740566 894740599
    0x7080f0f0906120108010c0e0918070527013f1506050a0614040b071502070309061407110f03070806101d070c0609060204030503121902040602100b 65
    0x1d60000f0244111011003038010403100e8400d0280000c2502c0d03500e003103c0d42d1450b1401003410850080c08d00740c60245070603101900403004000341402448c0042c0031228060742c0900c2c1075003014111903448030000070310002281c2031150701c03092030100e01c0c84400d0074640e03488512410004011900b040000c00c0303001800c2e4011900e1090340c0c4040c0e088041c0f000500503e40000c0250700341003584007101b804404c4640303203490603410080e03130f040350618905540d40d031103e0301c3c03c48024240c40001d81c03006480031070b803c01816407020050303055506540301c10071002030414086c070941c0241c001c000c0c58203100306192029810050441814400090120b90301c040d151a00103081400072170307175a10b10034080c00c0c5c00c001d4264509600b0103600d44d0f44400e4002402d0000f00105211840403001e01181e231549480310030028680d04030342c0156040801c5d81e0b194a1100060b40c010382d82640c0c4910000741041d0724210718201c52007121b00f100d095030014059041c01d041020040e29901500c0c47c0c0c844004110010b91 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 894743066 1250 894741816 894741829
    0x1218011b15060f05100903060509210d0c0c0f03140c0706020a0203060705031605030603070902030109020a1812060506030102070f0b04140d0801050108040c0504110d0b040207080f0f09 81
    0xc10120301c804a9018104510007039403e1191340058031074410011000002604000d02d8010b8075005200030889030360340da00603440d1101ca0503003010305610803000c40340e00500900c0500007007070802d42d06010a904c3d40d03504407003405000c42e01420314151030b400400040c0c058601130705040111254203040500e01100741d03080102d03e42c0a40003507000050071104602d800e110195100101e401c040d0b0030341c01c010161484041000d00308074140711000010074401c1d6810071990006190301e400941d82c968480e50502d029404c01d601a00c0400c01c060180304104610144500613104603040340741e0600902c2e15902d0292001a1149415543c2000071001040c814140108080d0103a505100349081a00c1c00c150f1840c0464012000c0d50001005040a140c0c044c46141c1101c000740b800b40c805407500c1c20444e20f2580c26034009903015292455202c00c40540740e01030410700300b980c40c041080b40c0080c1d01f840300b60301c181c0a00038100b150030443c4070744220018001c2c00581e10004403460030481d100020490 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 894744316 1250 894743066 894743093
    0x306060f201606090603060b0301120f030e030318011709100b120d0e120708030a03020309010e25080c0603130318060804020f031903050903150c0301081218011b 71
    0x2a8500d00c203005d0300390503002d01002051a4a54a45550b140103104100b908034204010420507003c6600000d05101e44c198200110740241903d50b01ca0705040441904004c0002c801c2c08034803015800005071074804405446207103e407001c0c104120200f5a107500615411092a0380401c104610000c504030822542010150646641d01c1e03880c0c240081144a0180c117501e5041c80d8444202401015804015101ea510881c100940c69071503034501c150150501007103030b140500c10380001c28003529076189500e80310002c0180c4190401d0302d0303504003130b10b591809282c641c0021040010400b8101e241c05940c40040c001d1901c0320750311000c0c1068094802d410742c0800002403415042c0310540c80c0104640e020700b00e088004100d00c105a800a1546e0200e40380040e00348640450712026581b01841080000c41d0031510300139992400d0040c030318482d00207000c3c241030f42c07244414802001c1e50500480d100c0c0c5c03000c00d1300490810080001100c404a04c0c2c0c4a0000f002160301702000021030f4405d00380e1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 894745566 1250 894744316 894744329
    0x918060f19150e06120304030201181203080105040f0b03060105062a010b01031a090a1d070803071a190507030204090c0f03051005180903070807120306060f2016 71
    0x1204036240424001c15100042c0006200e2220740c138601c17060010000469088981c2800e1031310514640c001c1c284d001d0300e5954040c2507018100d10048040540c040000b90580f84100c600b04444520041040212004140c1058143d8005001031010346005c1c0081d11030780106c00c0480307550078100c42c80d00c0c0c49080c140d003a00005079102c645207140c56825005000580e190409001e4140d102c1c1000a1040314000d0401c8010710790300e1608140c030405607103045808844641c112980c09542c0c002223503882c0e000c104180d9540360078002c4025030302c242c82e0a960040004c080450715003d80450410014200500313280709259003044006055241c60103910780414260700d0307039588111100c10207800da940003041c6c0c0380c4100c00100117000554400c8039403c510f6102003000e0811340d0395401180e245105004001c1e0403150040780d60f40c104902d200f8148080c010603a42409110754440c0140c1e5200048200c51000c90281c0a6034954244400402804a0090000c9031804915203040d0340c07142e42c083d008030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 894746816 1250 894745566 894745601
    0x30c06020d0e0607090b0319090f02060a0c0605010905060f061602040606050d0f0608061b1312120504141e0a0618060219080c1005090105060918060f19 67
    0x1030640045c40e03000103085103c3c4d0103203180340500b0807684041600b04a101c140750740700000b8051203415944401c107154080d14443e595241107030050850580d41c5421110941007800116002c5a140900e0740298009050506071410613001c1000d80c3c2c100707203250745039084d0411018000d80e50f94001c601c010301487d01d62581d950202d49400d415104003040040e681030070b00300200400e1400194650780041d80c100707140044503200c02101080d110b101000342040340e54030004620b64222040303c5810512803240640514071450080d201e80c0114403440034000b0789840c6510706c6050114040700b0321000c003140f0080c00e80c1071100191031041c254200b1800100d009c446d0703c503981c002151001c00380c0751900080c88096015074081070004c0101c2c4004044c44400320302e40015407010444070300c41c40c034659018815481c6c182c034114000c0404036009886a80b50401040c3c2a6107001110a04d07002084c000e0304041d5203640720740603001d8010300100e841060440100c04c00f08018416646181050440c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 894748066 1250 894746816 894746821
    0xa0f02040e0721051312050304240609020318010617070302131806051504063c0305010c1205071b03020309060a1706030c010203031803070618020a0e060a03030c06020d0e06 76
    0x9502c501c08030030b060061040420600001c11841c03032b2640001c8540828900101e00814405009000f26038000c40c001e0380080f00303020320803c105e0f082d104c10042500081010943e00d159a01d903060f403000300020a9085800140058105020252199913031482d011424400011000820040140c0151040d81d07070340003440030301c410705904e12740b000e038080b43d0602c0120305014140c030102100e1012f01c0f05007080004c210200c4603100c04905104d00b0301e80090200c45e07599003881030181131380808100000c2e0440244d075103568518440c0600800c00c41c1d8801408680422900e00a09c2c4070007010740a611040c014006541d60710340091000d00804d036500e105d4034010213183d80e50703403002a0285101e900401c0000c152643c0c00815242d0101e03410540e00c10030705100c5142c038210b01c1200fa000e00154140344c40074015224a038800c2380780394825160410126074680c7c0c2040c13a01d00944803250701000002d801c0000c02d209034460802c403805428014a03044664a580c0700715480410b102c041138018004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 894749316 1250 894748066 894748073
    0xe100f060503070e040e0c1903020907051c14010b0a030609110c010f0209090f0721020a0e0a08192906010207090e06270607080a0f02040e07210513 65
    0x30080400304017940c0c2401914000907207281c80d0800c61109601441020f001b41c10040700f0b5005600c011600541401c8541c100b11070010f04680c00f80d00340d8000d945001c81d45800c42e11880c4244900d0070445100704080381d0811003501aa58080c508040030191200e0340070a05644511528001500fa1108250303646000c1c141c2c1c5003510920014100ca05205001d812410b850340004654171504242c40003450340e903800c3d0f05461081070a0006d442e20b00c001401700061115907402810b01440d5a100d00f0380105060080101d0303990305000344151a00101151b00f006940000034260491050b0020035506211a20740c4d01403100305100031002c0c1d62848240711040d43c042c40500060030000c8010b0100100c010020340c0e542d0b5019140850401c100c0410220f60500b08582c03030304200e4007905540250808a8000b84500707016104458100e20702410050401810302c06c403011909040b072440f24542da0b0a100703031001c5a040180b0700c03620020401c04070083c54180726462080c0042c0104200351100c508 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 894750566 1250 894749316 894749327
    0x703110618120910050309030d240e0405150c09060c1e0601061b0c0b0c0f06010f08150721091b1d0c0f0d060e070c03090e100f06050307 60
    0x112010001c003040089682c0d03a10703030304130004281c0c105003082503403500c0714800149548504500c00c1d10303191138910b003101c0d1000b190606000c0c0c00000c46842d001c0588541381d006501c1000d1310028002e622850003004244058412694403605184009003044a80030218070103a01100c0c04225a070420664207149005008c0c503000248090070050845606100e005002d91902e00490449410610000f100708058600703550090202c4006c842d48031a88000d41956503a0b00c0c0728900c44501900c000800d01a2040030b1620844078034030024500100756215699203200050019000c2004010070420b12440144d18860382d0b0600c00320001c2c1d40d0301142840d42e5800c0a02090f8400e000d507941c0104500780b914201c0d048880380141160105807282d02221906101e004091aa00f03100803078242203114995015070102e591341c1e051290643c4c1d80e1001202c0304170031411b000700403480702c81c424030044550350390703555001a0081140e0300ca42d823180d010f094900210303072142d0002400002080580d981c0305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 894751816 1250 894750566 894750583
    0x16122a0219061109130209040e0d0f0309021f02030c0c0108070f030c020a0b10080730050a0204060f090b10020303130201031b170c090d02060703110618 67
    0x610190501c410003210880d4502080c2001034070803929056140781c442c0c2070320304035000c0f02030080010003100e012450710406900582d40c064031461910059070880f40004ca06d103d04003580365545600d180c0349250a41c020180a80b00340d03040034241d021008005a400407400c07008205400460b00d40014040603882d00017400c10315410404003034203022445400138203401d0030008604002c5400d10340310200305d18008813104040c1c20149070500348903c40401001010944442c5401c0d500c10310344424510b9042c60b8086038547c980c140592560b400156491811825030703220788140e8401c0b0802c0c0d00046c1c241c8034150041054036145007420070540c49688200010308005a5002032200b29840303000e9141c1c00000c100305180c402c2400c8410071a0f02c02e074440381c010341180c2640029100342030b10090040f002100740801c020904e00210ba4044008000e807032008200a001c0100300000d5824851540c1102c44101d040c40508484d40441d0813080c00114814101e0740c40b100496940c544800c1e1411940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 894753066 1250 894751816 894751901
    0xc060a020606100315050103110d1109190e0402060a111f1a01090b030a091a0f0f01030f0807171206090a020c0309040b060913092105031612 62
    0x501640c4001c02039075440480481b01c003420300064021580c0c0c0000c085108207849c0d2241c02d464003190311412020b400144c40b0035a01540e84c088404501520f0740714842850240301001c81c4140c0c005001490100000c201c074001901d840c16160640c0022540303090032900040003198005100e01c48a44010b2144201d40c00303454080f20702c45c1d1300c0f00001030a40005405030603141707000080000c50790003540c0c0255150b1580311010650710b881000c0c010340da15500b554000403080c102c0d8042481d0079140c402c4e19040e250403018140306d919195595400a074800c0c0307000c544d1100c0f09124940e00aa0f020003400288122030740310b00d85407030301c80200611103000424101c070051041c441000403a8002041c0d07206018150f0700052015003100000f1120300804918075480031f180001c40c450884030341c000444081c032a00f500c0e0900c4c5001d0119803c1d2058121400f0001766040c00000d901c007508203c00602c44549040002d003840c466200311081d038000009400002c00c220800100a000d041c0c1c1e1422507189 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 894754316 1250 894753066 894753071
    0x3061401030b010e0f0a050a06050301031101052803110d021b0607020a1106090a0f24051606060f08071a0c060c07081306110f06070207090e0c060a0206061003 70
    0x200000107001680d00c854814010900700c41e0a400d02c0d150800e82d00090240180042300f1a0327504d0768010710550007400200c0b00c017010000622100e500078030036035654240021455100658048007100d442203101c2c6003d0070540c65040c022040c810440092100c01e101d40005070f0750700154000319080301c0229101210542c40402046171a65010441c500c181e42d1140905843c4103541c0000390650240e40d002550048041340b0004800c61000e000c4401c48103551003507031140e1a9806120f40c08075011f418100860310400c040500007600200316a002403081e8000503849488554520343c1d148250805000d41d80300403006e104081c146004e524107809001000340c50005280601a1a00030180003010403001c00303c4e030316040001380d4082d03401c034a0082e1083c01413295241c40003040c0310355580d0702aa02d4000c003c04503101120205a9510800294004000041c078180c0002c008020001051655000c4c100184000daa40c001c010002a00c05900410545c1072110820a40742d040120010500d071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 894755566 1250 894754316 894754331
    0x3080f15220b3c040507020609070b0f07030f030f09080a0e040b0d06390806010309121b0501090b0a060f080c06071e0f120315260d0306140103 63
    0x445065842c080342d0900e6003c4540c40082509500e4107252418a040d40141400204000198001422403040c20b6030022182001d41e219200c1d410742c0710b1403519851240c0c0400c01840443e0140c2030f42d121040d000e24001410400300c02e11141141e80040003250488400100d0000141e80814500502d40088034100300b401c8019000500202803403100400700d5481d14801e030400c8480c1c92860305044a442203c0030907000e403d100e0341052032481c080c40d001c18410702c08034855500c40d120300d0f038186a0002421084d50b81546040c0e54800103001e10410702210710114000050081c06811543c031710403074030402039040901c0703044103403003041d0400401500c0c031510400004200181a00381044c06440c4a980c5580d5810100d4640b0103500582c4141c82030420500100a078166003141020700480b50190f0f42100300030100c0c10341d49100d40615034004003800c00d21107001c0801200008050031074488541030100b61303000303042c0040201c10802195941001b009541072015941c20490000d1900704840c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 894756816 1250 894755566 894755599
    0xb07021b060c0c0f061b0f010c0c03021b0a0906061106061f0503071704032309010f051c0519060e040c060c020409080c030d060f0303080f15220b 64
    0x10307a0460121881041c00300130002c05a103c150844100c02140017a4410701410340114640d80c145c1803122074a40d40c070f0b014015406501c2507100700b8021380d250f0301500340581441101801404000600da9001000c0140003805003154440c2000501642c4c540c01c0000c00041a00e46c10940010041d5000303100481954417007116000305c000440e13850742006600e0b80c5548004603402a500000c103041d007140e201c2400141074104004001200300b0001c00e40144504010002d0b0501415111a010038001c1d02011615401000985500040c0200300c9403420711441201060701c109640c000e01c00ca040e1b552084031a221401800040d01303d40e00106c01604240d07540d841042114485e41c81001030040100e41155242d03080030301c0c2035401081d510f46130840420516140c1d031040140359100f910348100019400c1e480d100140441303800d038894041540c0e505049118404005040703c00c10f80089440c0d01071503565005803d03013032048206041001103405546400c031a1a040c0c464801c1d210201440c200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 894758066 1250 894756816 894756823
    0x1403181203010e0f0a0204260d030b0a0b0a0e0a06090302090714090d050f0a0c170f0d0804140601060f1412160c02060d0504060c05070503070206090d0b07021b060c 72
    0x1000304e80310080d5a139607258400900440d000100340124000e420700c40780c8203a5990899207540c9605458081a01c3c070019802c4801c1910410b4000041141c00c11503c2d07980b20140200880900340007400800c5d940c002000c40440350001404140200000c1c402d605000d038045922106600f4040d0708094280e9000c6403601444802d1f80c46003105c80f5403001089010312210306c2c00300d0050200c50450321585040346070070205000307520101c0c44200d0700140214001952001c0da01c1c0d480d001d084091603541c0102c4403c180104240d482406280074000829800c00040b4024240e44c1e80e540110300b00c942c4001d105038604007043c292140305002c0031041060b001002c41e0400041d440d004c6100f20140e4017030b101045400341c041c6d4400008a001400340c403458101510071441800c04102c0d111010a054500f8041c40e0300282032584140103000050414034010821203600801d207079490740c0c41303a8520000050445194005800c0100c8a081070001c0d43c03007020038044200c5100b030805962000c1c1c01c0d076 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 894759316 1250 894758066 894758071
    0x30615080610051e0402030a1e091119120f020405070903053d1d150109020c070b0a05070b070914042019020601080105040f0209071403181203010e 65
    0x4105803c10096074024804800b404d824000a04255160320f0841007034001400d13003c20090b0451103414888808041034812034000341d40c03015102241c900342c0420301903e580002e01d918003515050501148400d0921491805a07105d91800480301d452841400150795024100c2c10a0020004040c00055400f0a032045060008841008018542a07500c682c080e035048180000c109151120f00000c0c2c1030ba00121420750006102000d0202c94030840365550f080b05030020000e10b118001400444942d800404860f81d101044418054503031004e26070035403007500c900c0080348000520f0402c00840016481e84860141071983d0070760729008540c20540040c00081e40b04a680d91340480f0300c070b5252407820002011138019191550283c0c1007031150451044545e40c0544104000010404414041d29201d2940701040040c00c10f259801c0c045149405404107080c0000407413110600043c4501030740c481c0b201407002c1c1a040e0b08901b21142410020b200950000300200018071003e400b00d040c181c3c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 894760566 1250 894759316 894759319
    0x80d0c0305011d0405100615110d2003270f0a060212090307090509032d09040c05211609140f0a0305030705070f090b1806041503061508061005 63
    0x80307a80d1113185c22818a440c0580c4040f04505d0400040340720813514203010b003216602d403540c062441e10098110343d108045441c4a000459145405403072034403000304c03441c09a55030811281403042c0c0581040e840411065920040c1c100c589810f160303440c0240701e54544800680d034280100d814030310020340342c000c54080c00c401a02c000800d0b1445403000c00c03d100013040c8040040015081c80d0345295129809600c0c0340d80d0140c5080c02c44698000814403052003c42500e841d030380b1b00710a400c2070102505002c04d0303a405001003402000d281c1c00401d54014009102018440b41a20704640c120385031101031030f002000c100745e11409120042c0010410000031310201c9140801d45240d6000400001c0b054000030118040031520f501000b00c006548016145006901900c607078407481c084085405450601da80000d07503122031900d1424416105411007005000803500003c42840640294a40d41c404c8448954520120101a081075107080152059002601c0da84c202008180340701c054078041c0d81e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 894761816 1250 894760566 894760619
    0x120f02070f02060a0c02091003031827060b030f07200619020c150402010201140606070b0405010b0301090f020a060c0c0923040317010509010b07170702030703080d0c030501 76
    0x8211a000c2c145040740c84c5e031b008200d40c9903071900c50503917100103500c1e200882c0030400580700500440200d2401d041541e0b200c156242500d8038200440282000f1b803d99288079982c0d0380c40200d80001c03080d000b540710b1114841850b15500f080d4000030280c09810301c07012294807640280308035140011500980040d440442c5010500440050100234030519420074184d00c84c3c2c0507242c00358519010740600c114001d0f002003006070610805440c81c60400c0305c031a03034409401c010042c00141d54100258000d4050000004d2000e208004242101c0e84007206a9071600c110b0302d5070085240200c82c00020b40303820f00e418490803100c0c0e920018120343d1805480541521405440c0c915400c0882529041821040002c3d40341130500b8040c040e00e8041c04000d000071005800800d0f203062041d445812610840c56103071801030b041d191841c5800c0b04450010114008000c250056030b010031201c0c020b18007491540b580c1c0e403c846040c1c011502c00e03100c0f44080c03608140040140c64448022110034903140c940740b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 894763066 1250 894761816 894761827
    0x30f100902180f130203011d0108010203220f140a060e0d08070c03050c120306120714040c030605030303270c03030d020c0102070b0f16141b030403080a120f02070f0206 74
    0x50013090400303c4119805201000015602d400340c0794041040319581d0454260366295560b2600b80e100c2140c114219520318204e0305448089403c481078914041c980c0b403001c40400c0e9030b0b560b54994a82518584643c04410404c003448100e10565098002040c01404040b5402030007a0030107500514a00a102108075068141070048044600400350b440a40350400d24a1000007104d8009449103400b0742d00002c0b004518440c00100e02040d607070043c060b029080e05100400020f8001c09155008254481200107280d440c10409580039030040c0c4140c503810012a080300503041c0c4403c2c2c40c00d103290300c10920007005071000f20844c0c121403d50040580c0c1d46000c04040e501a11035240018032545210b010094480b040b000402e0048010381e02e46000c040b81604100d4000c1c0072041c0c505007030791082100485580b500381c02c0e10541c1e0301d2441540d05040c0d0307a45800c04140c02004c1d0810204144040c9440c5400d04c9220f03c0241c494910000c60a09110b0f8496401401042c04000d018541c00540b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 894764316 1250 894763066 894763069
    0xc0e04020304200a08010e06010f090920030c030f060f070c1203020708040b0c010e0f0c0a090c0c081306020705150307030f06080f031917040609020114030f100902180f 74
    0x4185005e0079925000780081d0b00b07554051a5104024030548030003000744c041c0803540c00c1b0280181c000d61a00503403a601050391181a6010014440f40c01c940c0c075204412400e80c0a2b281400341021017050a40500f0240ca4481200400014000c203038400b0444110945000a12040c8080f003010495190041c0c035044545007001c1c1078891a08120316040d404640030300c00320300c15084100b1110f01d40041e04c2040680000081e81c94617403c072920b5116048890910910b20303a6441149401503600d4101500b08468076087c10319400130105400b0740c6c1070240284400c6404022120003400151004000c560607012045094000989407004064071140052440364094200502034490b000c29a02c0039610400c006580382e02c80d880317415021302102d21040c1d1083c05400d440803c1e40100c6407603106540c856480304001e101c80c2030200d040c401e500881010004150020b944600c0250708900c40d1030501d00c02c0c840449025601c129000b5004210b440030841041c9a003400f500740c1501c44084100c1c0950 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 894765566 1250 894764316 894764329
    0x63b09010f0504051606021b04180c031b0501020c010f0c05121902060a0e07061101150b0a0305060d020a1a0405030102070b01050a0605041a030c07150c0e0402030420 73
    0x24469521642084280014480041424082c640200202a03411740d91660700340d0312841151f00e200311050f200702c1c9004060910740c0002c1161031624401c0720703c41496598036814411550801d5907c0c1d60103000c11201c41005c8071000740503000c00d0000f48509081500001c02405c0d0103001c1c08104003058005500f004030403c240c0d024441901003280d12401040702c2d0b6402c18044028180040c42040b0205890441741e1040e038280d81c54800140c514582042d205031201d200001c01d100d820b40d41d401817020000c100e000085c0c0036000b039249499072038111000040545401a000c01d00c01ca000c41012401030baa020b15203001c43da220440600030140e148800d480e9406254020358255000103a104100700c020308040d030603108110740c020007454840804844d00d001e64060746800102c081c4040354a171032264060b562100306d1103c4207140210aa42d100c9a844401100a0b090b607207458008400f90342040c401e003211001601c0031400d510b000c0d1144801c403c030a0001d10b00307a00e02e0b69590252925130305c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 894766816 1250 894765566 894765581
    0x20a091a1c120e0120070519082401060203131401050f0c0a02041401030302032d0a0c020306010501031116050a14160902030412030f1e063b0901 64
    0x180800c152200e10070809040c0c0c1d008442600e001805000c00d242040020364040b1741d0351850390004058441c01d000034445030380c1107586020008010790100140500c0d080103a11200804014408e07512500054035828840060f0080302c1550810b200800145008034034420481c1e426840401416041c440160742a01c0f440312004c02442001071100c07126030000940007003241c8295801c012460151300d1741d000c007603401c0c000200141c008011649a1b64000a00c407009111300703011466408190780e500310380c503500008040c0080b4081030510025443d003804141c1c010a802e00b400e004504070340c141c003a1540300301c207034441041d00420214414070808001200c1034035803001c40c40d0100c841c190284da50b2241440d8070f040401c9407455011942e0750041c000d41e405140e215550460050008905078040c1503812050112640d890140c810880b2080250b000c0700c1e980c3d80300020f01d80d4280303003840001d1840101d5010a1108203403a0284041001c907002e84c039000c51104050854864196081c09889407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 894768066 1250 894766816 894766823
    0xa020d020f0402070f02270705090114070b040b16021e21180d121b0204060b0d06120c03120513030b060306130302071809080309010207020a091a1c 65
    0x411030400f0403402c0c00c005c195a0b4000c450018482c603036100d80c00c00c0301180e40b00b400728540904011612480c050340180c00c58070014141258541c903019540e103099003000c40300f0741d060005041840107004c4c505c12a02d401001001c110038125501410181da19044603500300d00001103801c88442c0c403982442096028880c45000e050b440d0456000c0000c3c0b80c120000038400791040030801009841c20016194440fa4840c103080c80102c60340c501941c40310a4990305403d0108000c45000040e030704c0d441450050610341c2d61813522800408041c808444480d0020304040c60054400340200d811603900004882d80032003509050050000100c03118000d91004000300019800c01104005000103074078404c8809034205c03002176490110005a5403005403001e0056000340c01d0500c0100040b81c2482580700100c100414445550350310b242e165401181c405d6210395010400e4400c610300502004010b01c0c000030b0134001820740b4948552000441d4407058803505034441d441d40079420f2040e00c0806030342c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 894769316 1250 894768066 894768071
    0x5030f01091703070e0f030c1201060f0e0603100e030c0712030f0329030f0f010501050f10021005070c050316110a1d04021804030e180105030a020d020f04 68
    0x54801595000e0900c6440848502c2c00c1c24500314901c001c0c1c001541c1c828540c95031014408040318040c0000822003500722500750081d10880740702034079891003202d422040e500001449601c3c2804051079035629400202d0a4000c00091111555000880342d42130000480001071a0082c0e80140d4518420059100603600420b0300004206a02d005c030044000d0103620340c2e140481801000b202207907010180501203403000e048103800000404040e000340c0d94007404072807840f2280c910491900c42c0c81e81e00321003160b460b030005005600705403a42c0020004241c8121604000240c4c0c0a51501c1010400c42e0800e592180040c2910780f00745a01944d468100054035607500f54182c40401c1c902c0310101c103403441036405650910310304150040b54110350510900e20112211050f0b0400000d002a01c140e030706c40060000044500314030903c25004600c03d455240822003030005008200a841100320b0301c5c0c1c0201001008076440200700c0c140c0381541185c24007402c6c0040d00c005041c03e651200c1c1150000d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 894770566 1250 894769316 894769333
    0x603030e062808091203041a060411040f0807090b0d033002030a1104060c08071b081c05190f020f030c1b03011b08100b030a09110109061e05040503 65
    0x94100922034014104c2600307990300d01e0500402c08040d44020740f0000d15088941c1484080d105100061036000800100007180c0c00c01040d0b118942a00103402440c0c1058121004012a000400000c401007600020a000c0030950b8000516a02d81110000c0c0c1403010718500b4160785000724414003190300d40c00c1c0810070350328681e001d0300d0000c2d0000c813203070f03140c180c903000300c07e8800100c6106440031540d103503840c0d05290055a66009103600001f008450b50104c80060341e58041c50b142140c8050301d01d4000070044414240210010202407001c00801d00508001690070440c0401151b60213100b10f0a00310020010010301f24a4030102020700c4c0800c0c0000308401a0a610100e40404aa400002c00c102110300f000101400c070360420520503202d5004210505e084d40c01102019481506000c4030380e081c40e0b072102d405009a00844000d0140c40c0e90b2900b1008008001c504003d0303840003071070800509814994050444140c0703100d02411110845140395401d40704030100c2d0302a01010742550400c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 894771816 1250 894770566 894770647
    0x90417130302030607021606050a0c05010e010b0312190507030c150c0f09150c0f0c0f051509091801060f0b040806090312010302041e090b06090702010603030e06 71
    0x1000d9001c2207109004000218110300d01c0000e800845a98407110361101d146804801d03031303132640071514040510886110020116000784500040307000c9800021815140d04402c00d800d008020420140a420a006000340740c5014000c0c81c006110608003203a9030491414240c0e15218684001444030210542c80d0b4844003480e0042e8a22414a445003501003081c400b083e900c2500600072a00c1134400140d904010502c241d164041d4203000d00c0e000d100381c1c0344546845203039081c290401160030a0b041e0301001242000328074a130301000725a0a85d0704000420000514811018190090718011052500d050820030b40c0420000c14032002401c03285039440c501c450441c1c0040c072805d400d40c01502c00080326140048219000b104c0c5041041c0f4540e8295402c0000a2000300c8000c15455503248050480690920070400b0450290b0901580c51418508011200e00010310040859040c51810000a038000300f010321f0380b00d41220b03000d40350b0401740200e06407038104c00709814802407000d050032000c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 894773066 1250 894771816 894771847
    0x90201090308031e0a09050a170403120801060207140d230f010e0c030f120f0d0204060e040b0301060f0e06030f07060c050f010b010813031116050103050105090c0702090417 76
    0x1d00d0640700405995954aa5086003140c0f1b580d5006003082c0c0003602e8020000b0b0031101c4d103100070000700e05840d003401d07203c0d2540340303202c0f0303800e41c10b05e011400b10001400050b804115003001020580c1802c00c00c44aa0310209440e4551140001c0035042854003e200040550080d40b5500321000200e40300c907142103041e0360182c1014802c0c0100b90207004018041414040ba002c03800d620404000c00300000d0305008400d003039020230190192084140b0400079101c0e103c0c00140014201603a07200320746046481000115030300c80c860103110381c0c5000710821540d40c5c80b2420000700c0d200c0f46440140f6a80d4000400e08040107000c1e051158000d040c40402c0c0301d50080110960313180038808a900b4489441c520038221010460a1408125501c0c00242410340040f003e4654500c02c0c84c10844840c00c00c28035519208083c0d10040c03507040c00460071300c0300d96071510070b1078014641110310a459080200041a09101d8200c003c1e01a41e116800901808680200c0c50410044e1038801c176680c50701c92a00640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 894774316 1250 894773066 894773101
    0x80c0f120a080f13080c030d14090d17010b0c0a020306010303091802030402011e0201090204050127050c16080c120d1404030e1e03120304030905060c0d0309020109030803 75
    0x7260203103010400002100380941e111360a043d0066200b9081ca4541c0030458100c054101c07168030041240d5914043d50f802818408040e4800d1960103060800c281410002e951421a040103a02080388401d48084901c1c5030446601c0100180c0c0c58480701b000320b042444101c0080d4040c4500d0000000b01580045080103c442103154451009056080343c01688003e48020740054031058000703010307519080400d034899005000004280d11640e01040c16100c090740722803c0410030140180141120180f4088552111001041149020030003050903008504170107103802501101002000426812079003407869440c00c644118001124080c0300381d10140424a0403030801d5404800c0380440101107010b5507042d211545d200e2003442c02e011403280b58041c2c0c8002010700305041d8210392424071a510010390342c250420f68a1605003000b901c110b000d64000e5005400422907991050b401040c1e0b0554010903180101d85810a400103c81d80203840d0400340c03c0920000a03c1030b0582000003145 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 894775566 1250 894774316 894774337
    0x6050f07030501060f1d04020c0d0309060b0a060c141501080601230906010806190303021e0d0c202706060f0d0203040f08031006020c1507080c0f12 65
    0x1141c0e03c80c4030403201285043d461700c02048401c0c2c480c04020000d01101c0c6200d60000d0401401c00755004480340c60a06450700d801c1c04207582d031469405004d00741c0103ca2130040c00740e650103445898004010408c013103a10340a8038140c01148000001c01042c0900210322503180e03260074084d6107401146d601c8440a111b02d1400500280c01c0d00c4000f805036500c0107605a004140044656884006541181c401883c05900920300d451100d404c0c00c1480049003d18047c1c1c1c02000203603130548405009450b11004500b982d0b12101d03880380303d15400b03880d551860350f02c00401402000e00d9411400b030820307800c000a0b40104484410304952b40e14546070320082c640849a034640c2c1c0c5804091201c10300c2a40e034030103920388081003e60f100f000a07030025604a442100049844042a01d60f10100d0f00b080d41e0030104440d03030300390401006904010007044403208548030913001003c68500ca000e407141c42c100400400300402c41004c4807070144116109a641c4505484000d80ca05684035401c0e0321202c0c420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 894776816 1250 894775566 894775571
    0xa0f0203070810080106030b16030f1b08241c060c08071215060c03090515070c0905010e13110a15030c020313092706060302011725020a06050f0703 65
    0x13008001401000304582d0030a49001d40c0c4e8840005100707040c40c1d00d410b00c005040d118404007050f000d0764824000b0003401c044601341203084d607070030060042c24003600b4030700d00340304040b06940d0b011041c512544140404460300c4085810840050305c034040fa940c00600010701e0a0640940c107500700120341d226281542d80c4185d9a00b58070401d030300b160661503260880d420000d2060007124040c21100110368064202000003a5443c0300140d05019158880f00034440045140030400071890329240240042c20024000356040901e690f8a4410045c121000054640700034024001d00030005c2c80801b2001d441065000e0315040f810f400080100c00980010b854107100031240e902c040169082245002c1e449501185800291300c050131030303002c04528103134081c01048a041601c606100c03209102d1840070400c5803030340c00050401d00c3c02102200604810400b04031001c03951307841091210300180240020000004401c03440e1026942004145034601000e1007044801c540109210f0b00440d0f809 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 894778066 1250 894776816 894776819
    0x18031a0a050a090b070806060c2b0c031205150310050906160507260d060e1302011b050f0a0506150f06030f0a09022e0302030108070506030a0f0203070810 68
    0x102121039a160260050704e0b203070045020944901e88454120900410050030010240041403d055201003c001d0002c40302120b2407809040ca00301c0a00284641040440080e8a89000d40001c0c4a188400c643c0d030381d83d0001950035400401c400451000c0a0111a500410500194020030703058400d0302d00c91085800060020040d5000c5442e81c1c45560342c0c107420414256a204003510140f840c004607011b040720940c500c100a07102500f0b41000109010907001d02d041e40440d400c00005e804448103c140c1c02d082409071b41c001030b40c8140020003002c0700d8081013850030901d040551601c1a5041c03401452030400510100041260060240315161407a44c60a2800c0140300007801e0901c4d80c01c90401e000145083c860b47c001c041d44800c40403000f007200000d0388c1c002486000c04558000c170b130001500c40c1c901c03d51002207138801a0001800c046145505008603a0340d60740c030503c0341512980c000000640310000380d401100c86074010b504103645a0038a000081c3c40020304890301c9200c15540e010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894779316 1250 894778066 894778081
    0x40e0a180506070306320303071a011508060604030221060109090c050906011e030e0a03080a0e070605041703040b040305010902010f0305041e03020c12010608210a18031a0a05 77
    0x1c4003014071141c1e400c5080c0b4442d0510f0980e100d0090340100c3c0c0d89400180071041c00b042c44982b4400000300301000220013581010380044140510883c55001c00c0f003880708000550b203a100c2250292030701214011000c64440e800d8505101c2001e048030b03158002d81c0000103401c140c42e00009092842031540320b08403902c83e001d0182e411402c43d0120b000504442100a40c0a81032000004a90749450082a14080d06940c0341c90001c070080101c0000d0049003c02928003040d1061074034001c5240c0103414010318280e17004145000381e01030030030020040c031306d9022200c0b4100229002003c044484d9130b1aa5500d0070220300802c00224140e001c02e10208801c52668441c0c810684103650051301c84400000032401454145038000c002c400f584221420400ba65030303411810400440c100c00081922403c103d071150600440e070300004016400e1511905241e140d207070a690100c0000d29081e28a51200300403442c14142642c0050450180581c03140c850b10880382c22203200720450302d01408551210b80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 894780566 1250 894779316 894779339
    0xd1b0306050f0d0b01210506010b181c0308150405090a0c050612010b07060609020c010606090501020a020a141c0803040507120f030f020f030c151b040e0a180506070306 74
    0x3007005013008910001131240fa01000e514061511080012a03100601d0750b807490b10348002a003120120020226a0310002048009000c5144400b900d0510081c10300c60f2800e1014192138400030107102c103c0c0d000807000606c1c0200b0751060030004000344010b007024a03859880c3d03c100345059075081a01d81c40480e05003040000c40d580d42252400580716a07182001c544891b4012080443d0344640b20140020568680c0c0081e1414164038000091064508072016000c1070599000c98159003005981c003000d03a484000c42411510f545c400284d09034040c0300041d85204000c002112201c141c2c00c0610b0601c118040030394440c900c00c004403030003191075105500035040040070082168010703404400001c0d101d0740d01c0c170b100380030f95004075200b61960380e03001402c5402c102d402c0005940800386000c81405030080981d0056010300400e50001001241194544591b020b02c07903034688540049070340d00350355900140f1084810402e441c02810f00c2d241c1b4580380c0c1d1040e41c01900183c10b000f000710381d261900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 894781816 1250 894780566 894780589
    0x1416080910111e010f0609051501110309010809071e031419020402070501060b0d0e0c0909151905040c0501030510140d06090b0903071203020703020703080d1b0306050f 74
    0x2801c060a8071003c081d00c1405041e00409035540314003181d901e55245004840c0a01741c4102d001c5610726125119003005140c07403103003504000b01390840c01d000000100480e42012020300c6c01c4240c0d566011034540c9000b02d40e83c01140e0780d010280b0319500e000001d08142040d00d118403420301c1400c080060322a52501c0d00300c84c02d0204018200714400501e4a940103005843c0b0400020030099554080840d050700854140a03010b0b4485c1301c80c1c0d50109050013a201106401c50300c0c0c8055092849903180d80d600b158500c20000c040c0300300844ca11649450011038005032150051141745001d24089a800c0903500c40d25022078205000b140384800000d070202d0076035a080e01003403090303441314081150a542e810b80c195034055a900b0400b02203a0016141807240002c0001151f8171074180c5081e0001110410104c01094414007410700000d50125268045a0700409c170140c550441c02d00c80c0000b8034504654803d501100e00d200c450098043d0845001c8038004ca5003481d40b02054001e003c0140c0c4407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 894783066 1250 894781816 894781847
    0xa0f0f0801050a17010b090103031e05160b13080304030c02010e010e030d0f1814090618012c09070305070906291b0309130c0f1416080910 61
    0x403e2000d0120034520003408030b10400c08400420380320344240200304c9a110a0304164001791004c600c280c0b02d11107103442c0115180c01484c2031480c202480d03910144070000c0701c1c4001c250602e1039001c0341c41180c24000400120380c119100d40d42e60301381071401038400d0301c404000303d02103039480200310a50f41c001e9001195050303015000c3d00c440c8510480884101d08100200d1050210102641e448850100c501c00e01820055041a04144145c0c04000710314030000c255620070780c007040407a00541d00c0a20054110303903600900a00c01d252001418180c1e881e81c46010048503030388810041500b100103009000c4178080e1003030b280141d0700e81b861041942d40c28003d841d0075854212909504051100110b1a144041020a400c003840c001045084a100c04829480c42e400400c02c035045240c0390350304d8280d00549110820044032424805041c0c003000d40013120a2040f0303010510341c2401580121964100e8052903211070a4036450041d84a40251040c54010050a19959842405a104000100711 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 894784172 1106 894783066 894783079
    0x240909060e01060f06140906070803040614070f0c02060d050103080d0606210c0306030212100b0d0302070e0403090806070c05102702060f0a0f0f080105 67
    0xc00300303807194050340340078010400e4111184880c0100d41c650700388062490f10140c0303824218000d2100e1941c204100240340000c2200b50030003140f03d90301c1600c003003041412101e0300320f0030340000320b658401081da0107021402540c00703500c070100028801880c80c2c2c80c1001c2140b1607410785000784e00465506101046540c01c208880c040c0c5030151200340340c5004602145015031808118404c003050341f0f5540d800d40c2c4900e00703110341c104801840d00540b0060b082803145a0482d91800310295040ca1030f45002550100340c68280a48070a00b505540100360081c00c0c24400401c00030060002ca050001c0d6910010341c0040502c00b4500c030b8155611850509940c0e42803090804540354810610035107880c42421515910b104000d2245010100c800543c0d5480d1020684c9840340c0e40300070b0300c4100041464803400b0b40c82000c09500c5c0c169503903261040c0d982c680003035880385428080c0550005 = true := by decide +kernel

theorem cover : BRFrame.Cov 894604316 894784172 := by
  have h0 := BRFrame.cov_init 894604316
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 894604316 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 894604316 ≤ n) (h2 : n < 894784172) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
