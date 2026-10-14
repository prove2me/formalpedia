-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3169
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:52:03.280159+00:00
-- url     : https://prove2.me/submissions/c2149344-ce62-4b25-9c25-79826fa109c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 569784172 ≤ n < 569964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 569785422 1250 569784172 569784203
    0x40504020324122808070c03030809070e0106200f0a03090506040311150408011b02060612060a0e030409180308070201140c03250e0a0501112e06060804 67
    0x914425844000280340c0c004c40c0b0103044401e103142440b100c0350850440640020300513a80d0200c2603100305803e40d10304042c41e0b024002c055108646540186120008002e62400d01d1a14408200e0601c00d031030a21540540040946a8100100a00241103c140da005aa404003640d2711070310040303011000072b103503801d021806151a07000d5500f52a00f004081241302042c80500c5200400980444030340c0c5010310002844103824080c404840d560303100700da810141400c038064503004025140c544030369240707100c0c4036005c01c000030705540c0607200d140007188400142c2452429440340760000a2060300380104a9540d01c543c07071100381c1e428400d9442d00b034941e456040403402c84054032150744100317081d100841d4640040e203000d11b0f04240c01c0207507140d48004214440d135070040903900c11000705501000281051400308221001020b0a08045007000204c803046c2d5102d00308040d100c0410b00000940306641e00c50152000c0b84140300710003c10019403600b101030b2403040d0440d0221604206003e291 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 569786672 1250 569785422 569785429
    0x90906090c03120316050c0d0c021f1e030b030a050304030c060f0507020409110414090d0903081606091a0405010b101704030e2e03090c1a040504020324 67
    0x251046000f01600900f16228410343c680c1c1c04c04c0c0076580d5000c105081c060503110903401d02c01c061007081e5a40341e51114400e2441408501585030041d25544440c00f00da680450b0342002124a0000084c01d803103488000d940b009070b0003807000d4048250544030703030310940040001c000014401d0341c0c041d160100c1a244d6500044400d24082602803001410501a107401400d29230089402e00348600c80020091002d0300100b412550480d680740700e03054010050203605070b014050060002894588505a9815522a50070714401c3c504842c00d8409c00051b100d041c8501c90384014640b603072005004c1058640e0650011100710140d809a480d5440c0c04442c201505c2c10300149410b121064540307040320411091440d600c090010000d4007800300c407948141c00e80e6901e000b800000280500f40e010024003400400c2001502030300381c8000e241c50800b00d4404686103020000440c4c10840220030003689580382100c190080e42d0165030801d00200c180300c46421121080300248040003880b0042e4100e00c001c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 569787922 1250 569786672 569786683
    0x250615030c090e03090d030f140f1e130e04020a0e0910050f04230f1e010f0b0619030b194205250b0a06081911090906090c03 55
    0x91b07a1050b681c4001e000000e00582d00b8621000860801c03400e10002c1161841d03403940320002080c00300070001518400031a4040d0364402c0c0c0901c0e0840541044005d42c03040c0a040c116014404801010b4000070f0210341d07a03003284401900301101c40050608240c14585c2d82ca44003c00b003100d00a041000041c0e080600c0741041c2e200e150800e039540c007401928440042c1c014400720700c1d07085034020082c482103c0001003220f03071038881c41440d0301c0d25542c0b070282c81a821280c00b4003c41c002d2900f091a00e20b1079a5501007540d0900c01e208204580c1ba191202050780200b410a40181d04041e10408100c0008107400013581182c0221540403c1c030540102000e01d0800d41c840c1c5007004142c518414905c001544809414210301414a940303000011b00e21a58000506522520700c007980c0d00300c0030f0410503200c420390f81112203038109022250030f00070010780342c10130b00c804603107030312000850802407050603e04c00c00103100c06054810035040c083c4c1c100392225001ca9174072035140b085d20328001060500068 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 569789172 1250 569787922 569787937
    0xc07032907030e011808091002010506150a11071409010e07020a060b04060302090f04120c0c0608060117090a05010e2a190f06020c06250615030c090e03 67
    0x24849991007120a4008124100c100c0d103040d982c030045c44c42100194030303100b80040d002d407003441d45400c0c58904009214003004d01500459040205110140d180e204081030600c0c0b0f000180707516400300d04022200141c514000070704c50302c501031002030b0b03c0c074032030f40c1d0b40e0303214030068034200c91503070300d1750381100300064260303602001a40102c0003240404c5080d48181380c4c4610081c0301003595a07403500011529482a81d51484803100441400100a080503901c196100b40341010900c6c03e40350340780d14000b44154424503017442038007800107841d603110304182d00b2404c0088180071906e00b42242020b641d0910740c001100c0540ca40f00d00852401d000084251040d00d540b03040040384581160807400c2c0b840c425582d16002501d820035116240c0c0301d60705803409080b00100c401802450180e0013840d05c624200124020300041241c0200e0000200292440b00c80382c07000b001480509203807200c0100000d194216041c0b140f03080100411180c0d02e882800c4445403001840060131071500319032240b181c0032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 569790422 1250 569789172 569789243
    0x108070206040f080405060f0d050a06050303120705040902071a060a050f190504141e010303050a110703060c0339081503190201020d112a060c0703 65
    0x40014000401420002100f2031003030740114200f50740c1e40013143c1c03141c0000f610801c080d1000b269180410050340318482d0b005100ca202402014648008252248910403800081505d5075000903c00c0d40500d08960050501c403904650305d44d26030401e80c0040600001000c401140107010903520700d0200010011b5039002445119003c81d51010483e0500613851400d521102c000c000240e1551980705a0754254503d407403240241c904103600859462103101a000603030300a50042c0003096001081d5441c0f069036003003880e424040720102614000a9500080115081039516a082507254121a50011241c04580494a11818403c1c616140300e03c100080c0c08080d40284030492140c0a115000404803650010448140c070200b03090564040301c0140100c14041214210b5a0420400084188600c0e042805c0700c501000b0340d0719503e0014440180c50655a00340e007044094941059500304014070081d030f07035200c046419481c4e00c524407056a04d65003078030550403d0074151800840041840 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 569791672 1250 569790422 569790433
    0x6010c11030a12031a1302070c03020d030c0b0a1802010309031b031e02030708160219080706171504110f0417010b06120106030914010e010b0f03030a02071406190e030c01080702 78
    0x4400941003902c094275000c0074030b003001015803507989031040b15a0103940e03420300025003420201c541c600051f2210716464078003e01219210fa40c610088106542443e0104643c9007078141150408103914100c09001e450f20140c0c2c00300760b00180f122a000d6100c200b042c0803041e4150007645c032402000c0d4064542207040128100c03020190801c00c1804c0d1008003d1481d0301c03417109801e6501582d03a0400c0242d0351003502c0503c26180c0103103a120070850380c02c0003400c4030710b4030040c1c10390300c91900303102ca5028a45882030340c07050b80c071001c003070303900d01440c0d40c0e4501d4555a541c1560b850110014a0380c40055213803820507581403c282007114614640b00c2855031184c0d1078620100d005103001c05040c2c46030015071044012200080c0a881c0e02440e1610012840d6000e11042200030702000303030810b00c20752040040786121900414076008490700c402800420941c08000309119206007604c070388400300c00c540e00003038090b003000305000c4501040d41100e2101703d9000c019117801d0801d40d03c800160340403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 569792922 1250 569791672 569791699
    0x1413062301050d03180b09180c120a0b0409050a0204050106050726040b071109240411090901170c01030c05030f0703060801020c03041403060f06010c11030a12031a 72
    0x803e600e0b0151601c207203000030341c1c2c86080c0d2191000c184c0582014000740c400044110043c904040c2c07106040e40c07140c002030598207115001e1302c41882a903c0704226044000006500b49002e90710550300342102500a000303900140ca0140e480d000d08010403440745140c4030001c40c03820f115074203032081250300504005043d107a241ca42e044003100564900c2040d20200000f007040c1a4540140012038030400c490001c0c00001400c000008000030300a0f04605000f00e42400904038000140032000003d4500003450b28041050441d144590200c8642003c107010001982208141840c3c480d181541d0035260344a81340e4004500f0746500c15001f400050080c008203140c84040c80c9280e400420314200068501d9960b0400e50980e04840300c0f51100d0b40000c81c0400c082280041c00d0050604110098000c61401c460a102900c401418150402440c0c010120420030400c0d25034207210001000c541040700b1500c0c02c446c903240c0c40c2200071f00007414400c40429418006210703404c1004001c0c50082c49400303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 569794172 1250 569792922 569792929
    0x70f020105031005030a060507031d030906070204090b041124030406050c0712050406110a08070f0212030f09211f020d050f100806010e07050d141306230105 69
    0x140000f41c01990054000405590402140381420310400c40402c4078944400301400f241c0484980c44c43e24a2810494482c0e0303236000c0110b85641400f12811034076603c250020400401d06054000c5c1032050070010301c4140045103400c0c0400e45001c0710307118544944812804882e1414150400910b6824008200011155004540d021901d44055800c180c0d00e901d40c2100d901c100d0441e100840c80019082c401030742c2c000a40c4048129280040c403024410b43e490402c0c51040c600c2c0540240300500c104021562681424011390003048112034580440a02004a541c40788140030f22408402802240403c0000302c0158410711290180080c5031840b2856a4100036000700b17010030990070840e00c140e644541c42620700a8a808000f2103d51a03c8031121032882c0b02900540e015034030030401000f88480c0700d170f0389990207042440d107152a0404030300310030302900440c0c91043c4443d1050040144d8005a402207803501c6c1d0203540300780601d101421921140d0b07850004106401c3c00320b10018400ca04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 569795422 1250 569794172 569794177
    0xe0a0b071b114c020307060c02010902190e0105010c0b0402210a0308040c0e0103051002091807170f01060e0f061317060f0c0406030b3f03070f020105 66
    0x84007526059400c50000f01c1c040314000100c1241d521a1080d46100520031034494200040e1025044000c0e6020f59458010b542c078090150028403258440c016103512520070742003064159400390136620002e0040a10000c1c042c0680140c4648461031400001d043d881303455481350b51600985101d0083e100d0390280050b81c10400e1203480100104910310388038031410407404600364001e43d00c0f8102420301d4035011549108135440101e500e030420005102003500800c07041400840c06000595980b01c0b1401b080100c182500b1a80c0050300300070410143d0742e0070201c0302140406001040b011030703403070303540d45081e0390741c20301486c000075000302000d101501700072050a0412500030040d41c103045005003030b4611081c080c0c020040c00b10410380c42d140011030030044a43c00c0300c000c00043e4501d00d0100c200c44064025803040c44201a240c07800d203480d03511481343e4407031451401075a420310a050140380074400030850715004a242da039013201e150030407004002d0f62101c9610007840783c000d8203240c004640c1034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 569796672 1250 569795422 569795453
    0x5011d070903020604120501180c23040606091523160f0507030210020102070209070e0612010b031503030301121712070216080d09031506090e0a0b071b 67
    0x1512207404405a1390302c00181c0300500460100714846c0506151040c00c3da2102c80030003103002c1050407501300144501c0c629800f43c45416170400d0f04191650801002044000d0703469400524200000c80c010740d120b940807042e02c4640d10000780b03c00e4112011030703213a60603c1c030b8112544040300c0e00c050f42c03032001001046112142000c00d04903940340d4a4210300c100f8050002c0311585d110140800850428030450340f00100c050000314100070f00c2e1380120f4042c450007071400040007660902030720036586510540e50800700e0228100055038450204014950003551865000e403802c0c44803140c28039002044905071890020b01c2c100258041c1d0700d01c480008100c946013582401400207444000903484000d200314080d50041401030201907540300c2101880e04880e0183d0810404540d00341e4008014030110380c0d000c00d08807226220307401c412008142d40d070032061751b5606000c5911800940025801701141c01200300004039240c901080c4c448422186541c01c0c042003a288034408940060404d100e431 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 569797922 1250 569796672 569796677
    0xe030901230d180b0c0403110108131406040311161403010603020d0303150b040510080a0e070803040e0106022805010b1315140f0d06140f0115020105011d07 69
    0x4191501c076014043d100c03414103000e09042031100000900c15019403864010b41c00065603450300e815030300e5404000142a107101c2c14011000c0105040c03019507500d03001500d80041810102d2030b40c01d01c0840e00c5407030030740741a4002405003146c02110103021991058912100c2c004c4105980342001d84104180346903800c03949950b80d8140000562141650041010b1103994005100202d41d030300c914580c50290042c00035103105201c240482d44a544181e848400c243c100812542d4421003088003078411150368a819004501001800c24030000240060358040158082d90fa03880b030400320781e03031801038103003a450b080071030103c071007912a94104088c11801140046400350114001c5910780c1c0000030b03c1000155a00b2120001602d04c4520401504c0a4a0703801c410000c035800107180c1e07004440009100e40c485250f840304119032036106c0380c103512140240202c50700c0c0c1008914920350003442080e0742e010030049c05030019407042c03007818161544112003503040442403520880c0210014083d105 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 569799172 1250 569797922 569797927
    0x504051e0409050d020d0201061802070606030c092306100c0302160608091c0f031d060408090315070504030b0c09090406021b0c1509060f0f0d0e03090123 68
    0x340c0c4503800307215a001d0044004180c410540d00d0024034220351080c041c011a4036058040c042046d0300450b1f00d02001e003149004d0703260a42820030710020501c03035000600080c0444800175000806801c001703001c202c080c0c05101e09031840c0e1070307112a10f84c00301e54280d80801d5100c146401140241d5003aa250b034068811100807899443d04581107002d1a00f0450101e04480d00304079900310f0800000c1d0541d603200054141420500001400066001790718109044d252001084a0140101131540441903030089601c1400c203810904040e0744402520b90081c010030a141c111070560441850141d2003a6627214030b040c1c550340701c40415120284c00701465a103f0040c074002d80d81c03885c003141c0c0558050000182d8035012020f4120003850300d81605400e5400200f09039645950301400400e8240c450820142d039060503800013280c0e0311464400c06130580000c9180f01c1c0801c24000a01242a033f0310004000fa9030342424510350f00e0050041d41800a040305504200072040c1c040d2145490030201034050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 569800422 1250 569799172 569799229
    0x809030c010608011e020c2e05040b07030509120304020d02040e0d020d0908070b160809031e0c01050415030e071701091709030a1b0e011d0a0b01050405 67
    0x1d0079554558003c860681d122081460008803065a9017646012a4011490040102103241d00c51806481480c43d25180051002e03142261001c81c0c9044424150100100c1c41c0ca45400c0d4105003054030740700002450000000c3c580200010702c0105800d41040a6081d607666608010084110300800c83c0c01545400400c120038038108104010b6000e1900504001403882d0340042440c007866200c08040d038407008003003080103411411035030500e0040da0501b043c80340c241004c5103107208090300243c040c880c01409001d0408240d0306241080094070a907440300380b1035001180d00b400766001e41e10f40c1612680880e440c0382d010b58480501040000c0c02d40c2c070140c1da00c1c0c400c5550303290110f5811801e65103a40343c0f4010410000000ca4040c03d14130415420400350101099490740300c038000801101400006d2192051005403400040c41120003d540c1c541e103600e40d2021605c542144001440440c1c8081884460320f0700a1107c2c80744107070341d11401e1910304420012448661160803d052a020340c040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 569801672 1250 569800422 569800447
    0xa030b06071a101d0901020c0d0507030e0415061b050d02030a1b05060103020108280c02060702070e0a0c170a0204031208041a06030c0a0806190615080903 68
    0x10541c250246022000700c07200c0390355070344140310028408402180301c0141441020400c0802c051304807400039008a2558803401c13100c3c02842a0002c03041345100b00040308080725403102c0240301080c8280d50f0040460039000511003625903080790a2803001d24128203010680c0300e1a201180708080e0340307004000d5100e03500c40c1420701c80d01c2c3c2c45c0c900050700f00040e04500181c0086940f148480c00d1b441c40c3d070041410342c407050303100d5206000c000d0410100305c002c84d1041400003000c21000030b203e03000c140500307000903a11000b0002c0c49803080160191800049043c0c0c00481c0030803c032003407549206c0c1a0341e1205654030040540a41003418040003035080e401c00301c50391004910034440000300507511411818503480d803840e034407100c0007000348040400002402050120100c03001301604043c81c0e0302c681300003c2c00c0100480282c2d030130504000d13000540d04400a0402c1c026440404069000030b14801e0040a031200ea00641c06c01c41286554002514440e80c0d07029407001c003440a9909040e540c0825 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 569802922 1250 569801672 569801677
    0x20102030d05072c0907030518060c0403020a09021c0b010302040902030c070506060603070f050d06030209041511181c08070c2303100c0e04060806090d020a020904080a030b06 77
    0x10031000509864140305001001001011180d0080c000e00015003540d20005c0c107a10301c01400d007400c2544a0001c00c12021182d038007140d03450b04110541da09860901640350701a08035101c10381c0b2070304581400040c1510a84215900114641082102006420000d0000c0c0602d11909030405508103c0019500c01d9413000d140038120b045903096a81d0305500b0564038003c000307890248590410018400c61503000b01c0b00036006042030a00c02d4840001c0342003200100119440650812805000c001c03c2003103503080821005d0380f003003003003000c141000106420750141c00c2805041d42c220701c0482941d450992141e114010354606142100d107c070347e54140c1d0740d0704441811106446085820700151140034209080025040c0701e00344a004000300213030b070322195416112841a610802c030074099104540e005030084002e0011300c8015545c800c0695294030480301010903002d122440102c1a201042c1c00d20156002041c2079a1030b269074444400316401440c1040c1495541c5034502c5642d21060007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 569804172 1250 569802922 569802931
    0x3318030a021b010908070e0a020403080a05120702061005091005040e1c021207020420161b030201050a0503091c050c0c0a050310090203030d1b1425020102030d05 71
    0x1038002d401c0030580384000c0b512034456850501c6442c1d142031040f204001940c41c211040764040c000c564840c65400740c028401e981019100880c002070308001140c11500812448203003010901c896965813104a03120740301592aa0310410740c656080080d4601441066003042c1081608400240d4400004080b1044a0b514103c950042d4429101c40c1d0b40c408001c02559255001800359070400904001151168101c000c0c811980c1c1c040d01c02c107401d0080120403444250610300c40e40c400099094140211401ca412146600901020f11000c1000c14000b41282d506842c0e1030b0501080103020307502c0f43c200030032a514622030799500b140c9a510305048483c1c4120f05072107955031514100c42e41824800308100a60082c4161542082203071400103072145480c2180100040e000c0b410b03c00070741103201d2568000400b90505240144403801403840c2410100c180d105c4003441828180c01d03060500a810546041ea1040b400b22241030101c0041482c103a13105105072890701c8145032001080311402d44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 569805422 1250 569804172 569804177
    0x40b030c0a03030906020d0504061b0809090403030f060f0b03040201030509120708030106110105130b0903120f070f0f0c020103090213020703030605040e0106030f080901141204053318030a 83
    0x904105c603540510030541e4414007840e101c2e1500b41000405031480c080380c280a54840000d46d4010148420744007602d007040b0005220100a060904004000d00007490202c0c003610724008000402e19208940e540442c3c911102d054110381c0c6940054004001c01840c0082d14041c00b4406121011500000c01c0c01070300c04c5015607100e504244c4000d2001d860500d50010b9a0f00d880284000030340101000035501703500c911030840d50759030710910703d00310f024540302c0a8005a0301014003003000b00c4c21020038410b0f1401d40d5504411440d013141120001413190aa200bc29011601c450241d4031a4001681050001e0100d04808604201800c201d0f4800507041d0006540c803036081c4a10300d400e005035501889a0700c001e20240c5c1c159140c4201608180301c00500d00d40340040c0012540c2d006050030302c622040402e50581715010704180b441c018a0850303041f1068010b00890524141145120103841203500022134455220186409055480544000b40a02003000003106c1460100300504000c107855 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 569806672 1250 569805422 569805437
    0x609030d060e0103082a03040b070b0c03060604121e03110105070e060a05031306020403081c110f03090114011409060306070e011b12080414060402030309040b030c0a0303 75
    0x44881200301c40903604505028501440104013143d804000d841400c1c0b002c2105c00f4207405480700c94914003c5000301c00a041c000414002441030406003d00500340c00703222002d00660399111158030900c0308075280340d880401840180410403010111107c0300c0e102d0400e207440501c2c149406204004a6241100098081c2e6107101811800313004843d0003682c1402c04007103407608000010514082c50581104101020000410300680c0101c2d45049540105085541c1ea46900380751320141e110b40d05d0412070685441d0380000c02009c078820100a50300440000f403c1c4902903059068661000d000c5400644d01e80000301400c22602180301e00034a8803c6030001c1c0c90350b105052002c144002010345110745c0245007001000360700000c400c502c110092238410515449906030390740c0c070707074504001405e80b91080420781d0040d80c010840c1070003103019041d444012a40d03225405d0b80e950040350001d4068000340400e94030b40c18541c0142200d00c00017003d4409500041000c949450f0140d40154000f4041 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 569807922 1250 569806672 569806687
    0x2001050a02040312090b090402090d0c030f051509120d0b04050a291008040201110708030d060803090109031e05030705010605270601050a030204031e060c030c080c130503060903 78
    0x18031110f141d800358100b600301285011b0900e110350181d40315460089400040c0c040c1103980d50065000215031002d00315440507120704205180c4124180122028071030300500498162105402e0361181004100070301241e120040d5050490300000d16280300c4d6511204000f4413551180919031180c46511000100d008450340b10b0000c40940540c0c241525101611b081d410340c5840130350160800c1141480700807038590780b00407111041c4000c1e51140e1800303003103004211001c02000078111506020340038402c82d91207800702502c1c0e12030016403074003255029404200080500713038020300860340c0740700c0104c02c1010760b1111400e6501c6000200c60341d2355580307820706c00391810000c5080400b4000700c41003d60001d040b20400700d0200582442d060000218001310340714480e40464016580c8410910750318850114950070f002100c0c80c044a40c20308200c0c070840950304c20f1203001841e20b12541c070712040b5292140446100c0d0301c4102100171004e00c0c94808904c54404028480c0a1002c0f40000c5682c0c405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 569809172 1250 569807922 569807933
    0xe040b1611010516091401120e0f0a050109020a06171504020d0c020a051501030b1b07210206010b03090705010e030a0210200105071d030109060e0705131107032001050a020403 77
    0xe550300016000121030f1b84580d12642e01c0050301000d84032001001031450800d902080c035200091409044c0c511801110008000c0103411050b5118400e65002900c90784071242542c000005090b0001403203907070b0340000c0030154400c2e06111000e0020300018a080240299202074800302594440075a202d0b8800104021007005122103400700e210441c0007030750440d50780000d149409001880c2141d400c1085032451100710048031001a0302420240741640c008140e820100e490001c11405401568000250102000100c074850011a009000128100340040d0740309070b00500c00d03d03050b00c101150b29006846200c03070b218003840c01ea19442840d5200041611070403002e207000c601c059041c44107015910707800000000c0d0f01003814400100400305c00e400b1900525003030402801c4681499480380504c44081040000d46034265001c0d02d0f01c42c0d803010f2040541f0702c40c001940d040c800070030410011a02c81c4d6441c0940c003202d8001c0c1821000710b00c85030f40c00d5800c03da50801a0b907500113020400c011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 569810422 1250 569809172 569809187
    0x302071110200303040f02132a0f03052203120e012408030405090c0d0c270f0e040f050d18081507050306030c0310090303060e040b1611010516 63
    0x100342c000310f2551915643d510880c60030410000d000301407942030b548840030301e1b400c00d42912104c5414002980315540184102c9954011a040405e500c0ea524904040c404e00a0a02c42d604810440707003084070381001d003000c00c00440c10940410074164514058100c0714011b11001110354400032503200d0b8019404420620403548901a55600310000c12001001006880448008681554541d5190362070700055208002940008514080c0d0070a09140c00092542c44000f100039031280820310302035621a0356084d070281c00c80c034082d00c81d0108034280740e1741e22a81d0f000740b0031b0b000c6581503401c55031010f1a100b003050303428022411210030040081d122203010310041c150b1030014116a0002004943c2800c805802001041000000140c0c145c40401081e6030074031001c3c08403062030190201d01c00040400640850029040040c00250301000080d030500850704034038010080c0d01c5541d440200e010700c00c14001c041c00664080c1090000080c81942d10441c40c4003072025500c10211002070003907 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 569811672 1250 569810422 569810477
    0x616050f07051206013606140a0e04120203070b13020f0901031112070f0902032205121c060e06030d090b041a0f0f040f050402040509070302071110 65
    0x10045140c4580460701c0001c0d10b40c0c11180344011241c0c400c01c80c0001c210340c2141c414581101003880c0780c44103005501681c0005c0445165419230400368603104c0400c0001c54113445444d01c40c0c48440045004984da090007e076108a1600440c1c0c5005000d84c1d0320711a5040440303450344040840ac087d9815810540050101c500080350021629070440c2d960481104100d00224003c1010100c04003031008200030340c50250803079507080e01103155105020400ba6008a4a40002410008000d60300300d803080007039001c0d03642c0030014040310103a81000403100d402c1628800d035104d1084610707258101e500e10818000d061340d4036a00b842c501c1c000085c1031810300c00002d607400300941003004001780b142c42416981642c0448100300e860260740d01400416006118400000903030001e00700340000c030380307100600440e80c0240c0036484031540c07103041000328001c070b00c00c9907040030440000618541c4170b6401000c070548903c0803040361801c010042044481d00e96a0784000c510218101410381c00542c82ca403918 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 569812922 1250 569811672 569811679
    0x807050301110703080414060c040810060312050a0513090b21340602032508040b0d09120f02010f060b0d0507090915150c030801050f0616050f0705 65
    0x54002e50b07018222103104070700b0064104807841c00810b00b005a0701c80a044ea0f9000c4000304ca41d681000c0501c1d1086a0103403190000178403601181e94110707041401400201c0750042007a12450001182c19289a805459240100442008014500b044160090010744000700e0006412481758007440280841c00a003280b4540d481c201c1c000c074a1500040103041c1031003041c481e115600411174840300100b0300b40034200158030400743c04224240d0000c0038100007020b03030444c040541d4800c500c041070030b880740c90050a508802c02c81849081102c0c0000d2241c000c00480008020805440703004820003c004c03804001034013580c6203a0a00d5090040c401403241c180c0d010090240380c60a000074501c1040c4044e040da980314000180050700070a6404002c0c200000b0910082103000180210000c0718000c000c1d01c12410302d914802d2501c122500048039505d52628100d036401c040800c1805000c0740c05090f44507500300000707046c4514070704010200710722603401031100004c0d6103502c0b810243c407500018007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569814172 1250 569812922 569812931
    0xc041503090c0618060f120e0607090f061b110d061d010c050304020d0c0f0b030108060a020903030d0e01060803180a0806090307030c0f02090c0d050c04060c1401021b06010807050301 80
    0x544c02114903601c01121404e0803d40e0b210710900c0415106544c90200e4100014501002e111000c0350101e42c05100380d2503a981c400c0344c240c40700c010843c00001070094200180f83c060b1800b075882c03031000d40c403500940958011640110500000b500c404c0007003030308440140c0c60742108030a601051418000566184000744030725041da160082440c08000c2c07001e480f461101c0e1a4005000306844500c01801901c00500c03950380e2514141d05203a8800c0c8181d4206214500004110f8901c91083c1c580c0c1250080c0518074102c03154501c44040d190818a940541d50390310800582d1107402c2000b040faa010f44600b40c1204070908041116481c40c0c2e03444546580c10040030000d01141c080111650706a050070281c03070112683c00c007000000e1242e24001d411221100602907400030f0800030306181051000107210302e40d00c901c141c100d0b5004504c907035004a0005007805e8002803407080c0701120820044001410f1100f41d6010001c0e200190a0007103c0c0e81040300180700d542d03c10b000640243c44150004d11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 569815422 1250 569814172 569814197
    0x1112010e01110a1b06090b04050d020c0d020108010b0a0917070501020c090f01060c11060708030910090206190516081c0921021905011b140d02030c041503090c06 71
    0xb4050307504121071503041c044c461550020400030f54000c00c04160800e10004c2c0b645400c1c9416035a408518200d0740252040a541d02002d140944800e920680d041e507a1011507440e0480c800c2258104640b08010300c106a00b011481c0400202c2d0011390f10390301e01c010455a89000d00281c14400c080d41032a029500702001c110006200504083c1100c0f8545400c910070007050070011100540c52406a6104200184007024000d001c1d018600400b25842a1600b6075001604601118007102d030080d00b00b1028065003652405800009082a5040c14035519251805520b00d2541d201118100c48000d008500e9400281e000170500c008440000010000d001c00d688441034000c0c5480c01c407807205100c1c00072286104d4070034002c1c0344511034001c51300118807000d8a0305c0c0b4043d2444d0360f41d104821400143c4446d0443c41600080903050505100070b241444040c52400a1f50004090358007102c82007000141c0558039080800e10301c0421759000484204504d8242d6000c10a54002400c0040715801a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 569816672 1250 569815422 569815427
    0x9140108010e0f0403090b030403030504061b09050909010e010519150b0f0901030f090b0105090603031809070c02090103151a010509010810051e04110c1005041112010e01110a 77
    0x2590050f418018140c120ba455141c2103681d9101da400c4000a8100402480109a0182c1206016600ca00d0050100c0020034044803041c5004080355000a0380d00701040196040c0600129041114600082020450040900d00b560020744100313088060010003c0e94010f84c501c14002d46a45031030010880c07e00d0008122003a028071125000001c000040d03003051a03000f540200341d44410104107100d90a0301381000305c91900b00f4403846014a250400080c090314000c0105c17800a0301040da40356484858400f44070141c640213100fa070901500303842400140e41e5210441340298030602c4002c4402c210b04003114252501440d40c51203102c0e07028015480e0383c0c0c014040d20b02c1400280307800c071000d544c1c0310224580200387c2d5101075005203464072040c10002520141c1e1410b10302c252000e100701c50f40a10394030300902c2496100c80780c1e60001d1022011514440e0801c940050184413442e0304849414005281e2040c03038400c40e00786a555941c4841504028040d0401d90031090086504001240901 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 569817922 1250 569816672 569816699
    0xc030d020327010309140307020f010201050714030417070f050706030911010c0c0905010b0403060605181314060a0207120206060604180603050307030305090645010c0914010801 78
    0x340b4103a840c14803698445a480381e071000d204d041e0000f1107101206001050a610791388a14401d1b400f03056845008000c070f5005024581c01100f103560f40c8030085240f141c00c68050303080034208039500c520115001d5182c1e010300c000740c240c06006006540b03840c0d8071882c040c0d207001d0740c2d1340c400024503051180315804100700d2a4401c010413000e003014102281c6a02e4076005001e2250000031100707140c1000440c2049400002d40140c910842c0c00300b08090b200c004000c42d0388075032442e000503641a68006007000c000d600c2c043d1030030b44c03150b4003007504210210700362800c19804403003640c0843d80c00704441381400824000301e00b68843c0c900103880c003400d040010559902c04c5018220704924086000011222039501482c0299000340c01d40b52031340c41030b1600a014200a4030942150300c542004240f11600c080c8100e40300350354613841c40b032503d031104c181c5101081c220380d2035440c410403401e10540241028003502e0022381c210b03603604641070304000c10101449501095541003000300401845030400e05107a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 569819172 1250 569817922 569817967
    0x307080f04150c05070212030301081501080709021e040b09040605040c08150d08040906080606030f1f1d0721030c0204050402190308040f1403031606060b0c0c030d0203 74
    0x30205006503660000d440070f228100c4000d41200d151f0482c42015640800035506958030039080e00c4089191b1104603c8a0b00280564405600007045c00c1085e40015801001011320240d001d440e600c1a40002e06c02d00e82044d8800c1101342c000040307189071450648240006040c0c115001c0140000c031003001040c00b0401004204032005030000c481150399011402c810740e5030300c41441c035034603520344005101411441c450405a0301c1108003103107103864007003550100c40c828600200340700c12106060607104020316441c001781303654a4181184400780d140042e00410103c0c0c1c010a461454942031121940e04041001d09036024a05082c002a41c09074041d1442030301111701258a882d18000034a08200303141c80b000180807072200c00410444288081d004485001c80c0100d8078543e1011244803100d004114158035030001c01c41800b8104a0b0340524210600903900011669280e5807282000d601034040203a480e40729401a54603450300301301400d4640103510203542420810302104600c2e407031031030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 569820422 1250 569819172 569819213
    0x61a090d02030309040e0c0a06020d0c06050709150c030f0302090f04020702120114010f060804020607150605212b120e100509060f04031b150608030307080f04 70
    0x154010150b50341001603450710304005008024002e1144580b03682e03a8000d81c4034500038150640c0c002400c0e4004695409286800e481c1d0000310340350303650751400030b05004008100740b0007115130126001e0340121000d19800c00d20385035651145800d04001d801c007114803c10004040c01008015803d45035015501100302c401e4901507210f407103903c0000c2035000700020706407481d80b0740148044003020100040c0e0481e0107002d52807100c240c40714002c580d20041110069001780d0b0412030580021103c800c0401e0040030110002240d603101ea0024000740083c200151600112490b00302c41c50005000641140d002c104221120303910007074203100802130000101d0207100c1800c01203034201c15280c0055842400c490151104149040b5000d801000c0940c0c05031200d100d21400076400c0040302080302d0007140c043e200c904100356421010005060140e03822110f4400e005a00300040c1a140a008040c0c220030000d16281d280c0720000500e0004018000700c505a0040140300105001408034040d291104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 569821672 1250 569820422 569820439
    0x120506011d040b040207030e0a0603090206090f0d0b070f0e061312031202160606050f090a15050d1a1e010501030218120703050c01030e06181507050d061a09 69
    0x980c0000e0080c2842503000303030403500006400c410140d00008c200d4046a04032074517980140c40d10021001c4401e0b504d0002e402c642e04000c00740052416810150b02014010240c0c02c401003647d0f51904d031082d054070120041045400103500c082d8218922000302101035400c182826051284011520164072554480c01d0600803000c00340740c410444040406001501555143e10503c1a40c010300d1b504901607441916009020030545041c14a421240c000244410450b80701d40344020001c141d8010b5091000743e103000002010386940140c0504180134000303400f000c0d1880081c03070b840148010140b00318401c0e00c80c03200148442580089040d60003c1c0780060b15230100102a841060700c038001a58428803d0340f03600344028001440341e050700c0c421000e682100f0b4000c0015015a5490b41503034025401c01d41c00140803286060120100400010464036000105000b05490030010354094001030000580c00c04400c0b081d009420041008400d1000511901c40d848600c0c0d005684416210f058917 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 569822922 1250 569821672 569821727
    0x1706040b0f040e0f031602040c03180b0c04180e120403030c26070501090320030a1209060203010e1e04031407060905011104050424060c1a1612050601 66
    0x804c458420107039003c0449695480c2280800c0c041d905501c4200c0c8103504000394464040d1180c022a009071440c500c0700110700d000d50b5944001000e009202c1d40d5180010700c4001040150441d486610b000c0c8514001080303024000301c0d50500c4810002d08091034010041040040e9000200b0300c0a9600545441c1e8150047c4070a06c0d6104003140840b640c1c5a0040f6102080c0507040d44941c407424884d844c1c0211313000801044881c0103802100801c82034005001111045002d040f42441c406c0c9070940008642c0c1d050307682d42040760000c0e0044250346004804001c4010000b85007005a44004040c540d03031443c1c2560000c00c0340e11000040398200750302245a9003040303d2a000701c41591741c8103000380300010040b40b50840e01c0d0081c0c0704640c0324500304074820240d605580d180314a40502d125281046600700035040c0d5010300030b04400c6980303501c0314041446000c10000f480d03018881e2225801d1691407103c100405142c226240c48001c649050103100e001d80e04018440e204981038224045100b15 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 569824172 1250 569822922 569822951
    0x109181203060e181603051902010306050402071209081612080705060a050a110f03010b03061f08070e01180612020d1104090e0613060506040e010c1706040b0f04 71
    0x2e80368040040082c0083c2841820f0103030500080c00100c8103003c8500c001050ba015407102a22848042c0c01a003040c414402901165610f076000c203401814041412981c0c0d90215007240d20005e0190380c00321400c021500469400120030000b0504100201060040f000380002003120506c69801c1d0241c407110050300b0080d505081e0b0b0055a0002c0030b480d10342c81d06000d194050003003100c242d540c1c03526050031404070490038800ea600a040e60170341c0c581942c0c03c1101c5c54640d5800030b041650700010407a00842c2d0060750018000c014440d40c0d56040a5042c12180542825840e910041c14170a00c1c00c025400328110500c0786044480c0381c9080144204400c10f100000d101e40f008c8200380609048404100000c950b0042044682c1910304029811070320050f1170b180c100c01e542c0e20001841d04400325000c6a000d8220310341001c1c00400010b46846800704550031100c21400e190040b031003201c0300503a42d0346880340341680a2416202400703030070b04076000a1030318a04000400e10495640c00740d8105901c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 569825422 1250 569824172 569824181
    0xe060f04060b030403020717030403030804141c03090b0a020408060f070e130b0f01050c120304113006220503040f0f0f0b0f030105010507020411030703060305060109181203 76
    0x119410b58699a41002e040086d140c16643c0622030074481c040c00d85881440e400400c480440350595100802625650344680107818032007410b21052184082810098404003a0141b4401598500007034080031440c2006441034002c020b504294030601c0200000900411090303400703403c0d01c100d00c4480e038810405803070301d047c00301c40c1980200c0308a01144a00c02c4543c00580c4120007103c0c2c154004019000440c0e81d440341c1700e00890a500401e40f00c2c4404200304002d1a00980306104286010300d800b40400c0c0c181c4085989046240d50038030243e6040010b4400d909096000e01e000313402a80341400c4440c290740f4003404d00110700000744032000140182032007500c2c090484542c041407001c0d91241a4001c0c0d141c2401942200b6950950024443d00328070201c2d550a515000358a0460303103444010740e020381040c442aa0000e44603c5003c003074961070001184075640e50744000891b5819828264500380b416044401424908a403541c1c08510100756500b015034450349031240c03040d2020b000c038080d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 569826672 1250 569825422 569825429
    0x201140901120609060f09180f14011112060d0308070c0807120e15160b06240307090b07080f09120d02010b091e0105060310170102040305160e060f0406 67
    0xb2441c1c14004128400c0c2078104108948603110300a113050b440700c01c2081100c14080200c00c40300d8060990100050380300c45d142281c00d020b081241d2a01e5030791a40e0900351055510305060300c1e80002020446510003003c815040702094841c0030704446a50b038081c0180340301401042c02c4c0300304900a80c04128444c4104c40e6460340c0106000340c6110640006010448087c1d031040c4101510007103400044820800c0d960701c14102500754610603043d490b0740c010800302502c0c0d80c1d00003c0301c80d4012003403080000c5c600054070060058554030b1510100050803201c0b150041c80101d8801c1001c3c1011a0b1080b003030780d031540d280d8200c03d0342e40c44880000508580000c40c8207d040d0180783d403031758202c64040d442660595002c0c1e41c0c9080d5a51441804070003c2040b603508140c803c0708400601181c180311016603800440d03003149074095915004070081d400340c208007511040c4c2d000a0280100401405480640031804248943e083d00b0b02c00c0c81d54070341c0c1000700320030300071481110881c010340c3e20340c0c2016005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 569827922 1250 569826672 569826707
    0x140a0b2208090a170303040314070f0f11041802010908030f03060f120a060b0108010e090d030e072706090b030604110607080a0503090d051608070611031303020f06040201140901 78
    0x300c6500781340903849820488064000c05c9074100300c8214003900d41f00304c0c1c0780b043d032101030005035450503590581001c061038015190010300c98181001901ca51003403c40b28045510410031944a03440014000051500625880d80044c043e6041114030807040d0b90700100104c660540d040c00c510082404814502d0328140e0503c18018180203022440d130012403551801c0e45d4200c0079a813244441890341006441d50078a642c000743ca40c0024034865841420b9949503803081e11011640c0703007081010143c1554919005006111141c0007a0140d4414400202104002400000c05d13800c0000e844d1039000748090310440002088a6656503085c0440d1201503020b80d4403600e40d0280703240200686c004a40b000c6507132050340c9006100d40e0003070007900d0304a182c0e481001030780880b56843c00c1c3d00e60021801150525141c1e0303c4513042070704074005584650740d0381c415901c4800050600078a0407040d00c0c128039454106001384005070364898500014403401880e070390ba0301c9644000407220b020f501c00368002c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 569829172 1250 569827922 569827949
    0xd0506030c0a24030b060d0c110f0708060a09050a02121006120302010b041a15040308070f050d030e0c0108271f1e1503140a0b2208090a 60
    0x180c041e91401d01c2e010f08040807005814501d800303031041d0f08a0f00c2140d2039590000090000e042c01442d682c000e400041e0961814080d022001045036140000300d041e9245203820a40d020300240c40e00700900c2d640034541c000103008690054403059103a111205020b401800c400c1525240550200f0404841650002c001c008103aa540b1070301071040029101180154204842010350307140c03a00808801b03c000032504041c11950404000d0000035401202149200510002000c00c0095024003859800303203500701d0541c440e528020b4200808180c2c203005042c900200040e00c1080016090351000080c00d00d03001d103451381c50f4061940100860b20319030400142c2d00c01c02c200c0901081d01800764007503c15005644210000e0078040d00c0b0070036a500e08001c81070794007050845468011a10401d551501030302c00703039113a8407801c5184000310300b039441580c00ba03003026003000b060b450724980c4001c40c000c148039442c41a00d0000030500c442a070280034144041032070211366440314802401800550f03000da0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 569830422 1250 569829172 569829179
    0x50d0318030c030215030405060703020a030f020c030d0608060408190905041a1906021009320d05072301061518050a050d06050a02070b010902120105040c050d0506030c0a 75
    0x50382000b180030490054160112140c0f91100c554160790051ba03203c1c000e812a40d8070708000301d000790030a9807108101921202c1801d10410148020a161103c00b4081e595405031360080c0002c0d9092980800230380d40c01041000086103819096070812200030068034103910181900f100d911015811581d4003030f10701403080c28001144a0400110401650394400d034075507405911415815901c41c0c1405600182c2290400148503030220725802d220342e42004102540b11116818044103642040540500048140c0345040402040303448000900d80300f490100c0a03900c80c050b0580e60000050304d08bd1000c1030340c92105007900028040c2010619155502c0094200282020440520701c00002900d100102d01030820340c08200035100054295003c00745641e480c02d0080c10024011400c80f50300340104030005040c5010719008041c4403c0142e1100424450300d13220780c0041c0d1250b84140d18120750394003442c0d0482c0c15590a0201c03600f000810703030348150100307007002c4442507019885141400c011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 569831672 1250 569830422 569830433
    0x30a030504020f0a14040b030606030a0f210909140403120f0e3c1e010f061701152403141608010602060609011502190605011404020f04050d031803 65
    0x117800700e0804890620400b14220141521400f00741c1303c0a8064000051a01c003103550b01d5850185d107441510407995888140f80288540a180720103600001e00c00351040040c2c0d401030160526406802c541c03291241810364009c0d04102c4113100640c400e98861210f044040d58540c00342000800042c183e40748186000040c1c031810094041c00740c0001401c9003522042000c0e0b030500601800804024000f00c1005004902403a0760344520907110342d00d800316001107100c2c0c4d025110082c1440507081c0b400000448072242911501180600c114843c5c803010031010301d4003242d69903070980e0380d01c50601c1c42101041c110050140c2c00b48102a0750410814013043c2d10002105175654071007a510350380d0603620f58100700c2c0c4441c0d0946050340d220906000520481260450309403590400d401210019011918618220190f0381c03001d580c00c55591004001c10a840c502d01540c240c000c58045150002075401500d01d40245e0189070b018050341c4418004241c025800d00d0002c0507901328031048503940380b1f4203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 569832922 1250 569831672 569831699
    0xf03200c1216031b1a07020103050c04090c0c120806090402100c0b040c090c1d100c020d06241802030601030908070b090d030209011e1407050610120203030a030504020f0a 75
    0x60040f003203a43c00011040f041204541c010718170184a01d1030f1203c3c5800450150a02134a0421980401c101c0041c411030756100d42c0700300701456112850b04454038202040c04480782c000c0c160500100008001c0c4503502d12038a1640150f04440005154a0700c01048450b1410400024440c00800041c0002c0c01342d07031640c9608132411801c1c103103c40201c80a04990000b440640342c1805124465403e204d450030040590380045a49404a0011a1900007034859012200150b41e01603903080c20070342a40700c4404820300c40382903240309403041c1d180181036081d40c2828611202c5840c5d0101c081021a03101f50010650b9580107a4070a07160003ca0030601c41c1ca0205403400080b0740310f03400002c6002d078000d00a0f1014100141c6842012015950844a803a50a0958030003007081414203004184da9000103030000c40c7c081c0c4010080c900d0801030020383c41229811250300c83c400ca100c1c0300c005940004c2207491201d078038640880c0c070f034407544040b842c540c40540d09103134449601c1d2800304224418840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 569834172 1250 569832922 569832953
    0xf121e09021e01050406030e03120a0c0e01180611210d24050904020a08010c03020c0c0910170307050d0e0405130b011a160f03200c121603 61
    0xe510b501100900c1c0c0380d072240500d0310200e070301042041c40200310035402580311403900c0d21002c041e42d01d04080c2005180310f8002c02c4861050b065560004a800c1903803100840d030042038203003072842c8840c85a40514041a10a2040c10204041d03480d0401c01168180100d466031824100090080e146442149485411040540240340c4c600620030005056040d099250240b0342654200c804d801c02090000703d6070000d00980c3c1001c8070200015a000c0f091141c0040120642d0f401610f840302000c1003810907085e5040e10b4410700020741031011480340419004105ca06100c114603820b1203070008a410f40c0030340700e00a051801484042c600f0203030881409506030100300e4040007195200c4040040b041d80041001d42030403003200041c4416590350128a8402c0c0d8840c0c0c1007030400e0707030260b13001d00780b8580c44004035690b00022a04808052b008480340c03036110622440310034400c441c07440090303480746000c480500c02c44451030171510b001c02c02d2003028410f010800304100700644900300304044040052 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 569835422 1250 569834172 569834179
    0x20d020d0306060e040b03190813051e0f1207060201060e06030105090c010e0d080f0a11122d0d060f080705060403080a111501030201030f0b010f121e0902 68
    0x50400518468402c20080c0d401c903484100601100c002804020000d00040310b0300740c81012010b0861410040c2c2c1442150b1165001c00d03912030b600c41c102c0361801c070641d01050041980e0100100b05848166000c903100710180c890010f850002400248078031550344105443d0b020301e14000c522280d064006105440e0406185c04aa40305c58080c5403c813117040312812960b0700304c6440c41819600c030350017023060a0780003454040b1a4400c1d0f140c0b0500355010002d01c808107030001078a080700680002800c250040003c02620f58034403240140661441040004001c9064520100300e0003090a4808190f240c2c00c107034001c3d11610506943d5000385903d0144035034181c048071001854040000b966030588070b001c0e1095080514550350085c59400c000c00c45024086407004102010f4020001c54402d855140d01111441d403450001408407900f480f0350601d080d04224480340b669810241d02c5c4110700383d916050041c21000034001004202c2840e061000625010b204a0482010703046042c05a0085 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 569836672 1250 569835422 569835433
    0x120201050907170606011211220503070e040f02030307060e15010b0f070305030603013c02030c09100c0804150e030303011a0f041a0a0e150306060c0703050d020d02 72
    0x100c00100b03000382c050316081c40e0b0340d0040002170b40329442581d100c1c0010800030000700310280300588807071381c0d40c0201d1410069401074202403c200035503505c03208001e240640c040c0c1500e0b4181880c0d410201c100400103080c030343c203100c09031f021510100f045480c225040002007000c005203020701511071000403c0030400c52070850001c81c6094a0108032510000301d800c4442c0380c4405660140e980d508000c01882d8155030b201c4d009004245140201c50003035601e5108510214800d1080281892121403034400442c418410402d11502c4a41155002d2808582614040703c0c8404115036414480d1350040c0300c601302240c00502d81d040d80c6101f2501203299255171407201d00072070034940e03240402d10072041c0c0c80c03201c40c1c540e003680140040104900c8104009207803a01e84c0b900701c500021001c81c40c1c142d00c600d0b000a502c0007040c0d408030056105102c111059040010282d55130025030001400d49031041c0000940c2c20150310b070070045031000715840000d0f07581da040e0800d0040d4031908202c2d208405030180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 569837922 1250 569836672 569836679
    0x120103110f1309020103060315051b03070e0405040618141207050a02210d0504090b06070b070e0d1e02010e01020a0302060106081e0a060315060b0d050c07120201050907 74
    0x2075140c0280104025026031101007940726070748050701003940c0c1130781851740c0c3d508007001260076039080348800140714101113601d05041c52100c0400502c245902a5114148180b10740703603522000154052004940c0800e482d1541c0c1812401450402d03002c03548800901c00c03450400c030010310b06222a00303440064410340d19281c0c4500c8114801c1b00802402034100600304001803402580540c0e103c02206d14a40c4d4240e10022024500b40a440e50100418800704007004481124001c0700c1c110582038449500305003540d91010261000540003a040c8180c01d043e801d001e840b212040c04d441e540103214280c0d400c50302404201a101000c2c1c00340e0003e80342d4026804a0f50001a456100c17641c5a8020003a0303a00e0203900310365140010301846038085200108258454201d070605018040000001820503d03510b000820100c50300416000a03051480c00c10070640e10030300392108100031071004500c2d55a206272226051040800080010020003060a0305a070b055200a00c1208100111100c0f140c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 569839172 1250 569837922 569837929
    0x40c050102010f020f090d0c050d031806110a0303051f031b06050408030a0e030a060c0305180d091202030c03030a08010e01051e040b0109050a120302060f0609010308071712010311 79
    0x1ea0000300348407105c00c001104071401c0988a41c0602400303698101c40300c0343c8a8001500140ea1104103400041111407610142c0a0b0b1404503c0100035504000e035541101046103600d80e80300b030902500b81541d0340006118040d00c2e603040c0041c10703488841510042e0712407400500011400c01580b021a0440070023090640c007543c12074081d80c41c500020b40c00c0c0046103030210340c00d00100820307641600171030005070001501ca0261090500190f100403030189060300c00d0380000c032500c001d0030b8590f52002a058414507000b1030f0713650a88901072030b41203141d00c10380080703441c00b409100c001d50580300015074107160769030281605042c0c585417294445603990340c80c10803005001685076900340f814203445c04c3d40145020751201c90700b0030040c14941130403030b9108005020b42c0c05e998000d404003041100880c2c1003580c18410180d00803444140301c2e1560803e54085610000140801003400b600003d089013413003a60508600c031840a6287d080d642c14421710300c1044604284011115103409080b80c001514 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 569840422 1250 569839172 569839177
    0x70c140c0a0b0705150403092102040213050915010519050712020c0108090a05030901030209040b120708010c05030405070b0a05041502010204060311030601020c011b0f05060603190b04170d0203040c050102010f02 93
    0x1030301039072408e8640b414550b42001c202a45c0c004a40c030301c0b601010500042e00c8130f00191249113280c0c281049074031320744000e01000c80070041c044070814042030044201a80c010741682c801c0049600b00301c01c009510241510795226500014100340f040310511203030075500042466161070207030f0b613000103900c2d00f0314200d80e0b851607900000d12a0304180206840c0c0d512982c040d158003e00208085514800c5101181609607041d6004800380c0101f0001d0001d14401d0041a03000a99450554130318030701034564540300c600a001c0d001c1c1814000501030059071082064501a1482141290710790f501c1441c003038001e50161080300042418003804442d074018400c02e49104402c1a005040c0402c203403001151000000d2800c440c7d840c42181840000c45c1124650303030003551041c4003c000900b400c10802d031418480060381ea002d114400c191600103444a0b41340d64102d035001120100c404240d83e440c0107180a103440c010686403000c000c10050040031102002258802c1c1c0080084804201d019001da2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 569841672 1250 569840422 569840431
    0x61b0f0d1b06050a02070210021c0e0f0f0f090112170724020f04030302010203010518040c03080a17040b040303050903030c3c0d0c08070c140c0a0b070515 68
    0x80c00040403020030740b141c12555004803240701c01850030065500103001c03010f02c900d0700001a80030008a800e5209140c80c0070101414074142170030003c0c0742c000022203241c6d81d008068042c40742020b2101c036035181c0c943c0c01d004002c00149102e03442e6842c0c10801c1d0341010005010795040a01030b80c0701d000c8000360011030304019000300b0708981560414081070b85c802c00300700a210103aa4208640850406004043c001441c0f0aa0000d0790300e526100400ca050404103000b00c540010420074000040c40c1e030080c91b801c5075404002651555a04201950742c0e49070361408500c0813000c00c00b04400c201c02404500d00c6144242c40801042e11080400c40d0b90303000445508007a0042003201041d00c0d82030400c03442558084038802a0b04044025a1a1601c3d07104801d100c0c1c9000b000c12031110f422210b010703030002d1840602d041005440c00401c010940f042d00070010b440c0c1401000007800310b90b428805030402e10720262080c20003554607021115141d022071000d85040c02280000340441c209200828000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 569842922 1250 569841672 569841707
    0x70804020108160c0b0c0405010201060803040b160f0204020406050c0f0715140c01110a1d0d20030609030a021005040221031b0d03181a06061b0f0d 65
    0x49a84456140d4083d040d11018241880300d0540102c000801e2070034594401c0c4c5118101d641c0b224640800a820b6a0440d001018aa0424070050011030138000542d0004200c140f117030300311480795051404811044441c080c0d00103000040c08070b15113030018020407403070082c0422204180d0a040d50540ca4201d180074200c0310384642c0030000503084c42580c10100d20340440103820326142a14541c5421103d500d080560844400b148406450707030000098580308004410104060310480001110001c00c000003c042c11b11245005044188914556101020250840c0d43e5030500502813581ca4118211007001480341c000a2040c5022600070240030300e60141803403085c1c0203c181503000f04c03100750840070010310092211210144020300c001c8041002d4401074214081d2034035000f020365007541001c01d04005001e05c0480001c0a4061103a903280300064900d520f40c5614000a00c50300c07500712006007400e40d1008541400303001081c400504054a000c9403400b21100c0b8080e125003050142440c7c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 569844172 1250 569842922 569842937
    0x905070e0a051e180708010b090906070509060f300108031606020c150c09010906170a0c0e04090b0610030c0813171209060928170403080a080708040201 67
    0x898030034441115410513800d045129088500824052038404280d020300426919031805581d542050840290018401400303804146040b10018099118000a4901400000541044401d03556050750817490102200d50b20302005980c41e01302c0c180022a0b03c80000c904140005004e002c0002107500008440030355081e0080e46890380750007500716444500681c000c481c50300c12a40050003c40f84541d07100c1250a440703500b164001071218949030012400d0151910603d43c0300e60300b01b11595407114110001045040184070304444090854030050b40007410181c1003010058040c1204d4429107069442401da0601d00381c04030103580708610fa8001150090b004aa21040410f0440d4007890080b410280e02040040c00682c030340c0c0c002000400c001010301c0a10441c424103114068100760048000c0c42001034260350400200040e07501c40d00707002c0d01c0017401c10800003070250b0b640c1c18100303907e502038803681da81c2050106a480321061000241c2003c0000d800300e030141c07010307502854045e502c80780d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 569845422 1250 569844172 569844211
    0x105160b042a08060f011d1b0301060f1b0218090a171b0105060f01210c020c030d08270a02040911030c0d0f11060d0905070e0a05 57
    0x3104040c01500c00d551488102c0b601c22030907801000504010601940801c03010780c54084018180131005d000420581c501500410001b104119190080400c00d001020141c0f10b0809030300b91803d00c3d030480100c00401100000c1c1d2240c0049888403a0b44260300c98060b01d0f001001c210305503440c4248020b40c0a0006490489080420500b03250301240000032078820600a0f00c4032609000e1440c480b810480c0002049140e8031003d1400340696499017001b07100394103006d8001082446080700d000d0402c0340494000c15625440b210340200000310020030000c0c0441100025214400c25103518080c2c800d03410400070381d61080c20030600c591320342403040e180018a4000c00210140a12200c20075204103031134000560b03511307c102800f1622958006540b00c0101c0d051600741082020038030703c140340896801e0301003040e00000d0172045074802680c00c0310011030b0380054440d0040c03025000689150032140010003000017116000d940021685180319540c140740c100a90b00211004500710a08a9002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 569846672 1250 569845422 569845433
    0x3080106091d0c070f0b090c040b04020a020c1504120510140702060703090305220512010903170a0e070e0a1508100b06040515030a0b0d0201050714031224010516 71
    0x2091080d101701d80f00c080042c09074070350300c3d400582542c0039101d0303400c40301d9515004d25061050300340d0f00313100342e07820740c10a0000032010b034030b41c1c0803800400c2c080d1228080c0300750411048000c86002d828001e515404112050605a0392000c4071182d01d002c0034a041d0f9000c0b4890312800324948540025070080000b5034500c0d0b41200508410300c01201400300a10007814180c40207003000703015043c4c504250007070600d40010042c001c50b41e001c0911160745080c50100c04240e101506620390460b0b52050106070b02e6010002c8000c041c028000344e0076000c2c10380c0c0818401112540ca601a43c0140c109010802e20700c00c041010107080d20408415500c9800b40e5180103045410030200000001c0c03189007030954481c04034541e01800f20004820382c0c00041004240c0c0250720600783d4400c0c0c20355502034018503560003e8034920a01d4800307490406044407100c0b01050400860360201084840d21a203414541801761280d0f805520400c019070717001480f4103142d4400c034107585019100c4918000001029181c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 569847922 1250 569846672 569846677
    0x30c100c08070c090e0114090d03020705031e0c0c0306010e24060a0215010b0406050418091208010620061f1a0301050a090216080306180403080106091d0c 68
    0x444080d0070a00502c408620015121001404e0850004c1880c8149455484c05c44008004131400c0102d150180140d10000041d074412480403814016910409810014034500550384088100800700c180c4010000c0100b01808510900c4c80032581d003040310204040d1110400d00522100303610b07100000d01911008400c8540441e9026090358040c0c1851000c2020342d8050f4074144003592059001c04490994001c0c0240100043d4000a04280c00e0150092180c89544140c0c0e2a03584441c5401141315007035480815220b60090a005803c5003aa0002d40006801d1080c0c0000c03031007801c40304140c40c07001991300e440303000010054103003617849504504103004804104100f115001c840415a40c0c0e0000c01461481150000f0301e840c3d41c908800c00800c401140c1203a0080d90050044001080380303a49004543c42d0b1102c0c0c40f42e144c1c3e5444012a0300c00e2104a40f01a035520804d0a00041c9074210300b14605072031995031505d1016480300915003400211926080d98040e003880081c0c0c0031000c1201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 569849172 1250 569847922 569847947
    0x303040308040f02030a03020d090f0e06040c090f14040606020102030f0a0c0327050105280b0d0b0f090c2e050c06040605010f050d050c01030506060d020a080f06030c10 74
    0x56030320b03d4541c003ca460201208400c0303001d41d0100c11750f040903030307040790400006103c0c22900d5071b82d680c1803428001081c0006410303940039079141d0340d00c0803115010742d07541e90141a0802e60714500d9555941c5c08008000328001d0386016074946403012400c14418001c40380300b51101c0604118940320f81c1c04041c02031510f0400c0d1000c043d41c5c0c020b40e9020180560030400c0b888101082500c080105007801421283e01408030052003c1441c1d030042407295070445a00e18601c210800941b5100c4030001c140760700240c100c014016003d80d801c100d801400000880c1c0a002500202d60032007202c40d0600200e8070380c03107042c942000e1b1140b410700003c40d07140c52038542d440031f6850070340c0c00c0110a041007490184240d908403000e0f07031108014070264003010581802418100c441115007100e81d20341c0c90300c40a03c0b807a2503041549401c0080c4140d103c0ea0115504542040f4046540da030200e00d0040000b8030665060321403074110008074400e850b00041030078154900516001510928660175501c0300071855 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 569850422 1250 569849172 569849183
    0x204030b0720070b27010c0305280201021903020901050409200f0703110706090b340b15062a031809090f0303010501030e0a05010e07030b0a060602030304030804 71
    0x120052001d4040c410200103040c150b608a0b100c1034000800f181200400403805800005101c541103684c0c7d01c018410b020580608105554003030759180c8140e00c0c0079010180c0801225042003440e0a5415802000b07214540a440c4104001d0000110709a100d40e10045000400500080c13045811651204024064020081d80c42d16444032012216030066401114201170214821042c1608400c82c5002c07140481c002c2d0801c141030620203001c0a00a00640e0b05020307012170203001d03001c480307408100d5202800d5404480150100d10420078590807040450301c0030203c0001c42c2907240452189400c030075004000c0c50030481a01d020000182440005580102c0782d40040380708078400f480103180000d83c1c241840e840d00b03000f800313010301c000c005008031040341d1101c1044030b0f600c00b021017a039065030024603003c204042c030801014580440c0000c040c00075442c1080102000d00000390080440e4401c00e80c0188036902e0b25604400c5035820b02c224800358000f00300040019220340d09841c0c1c003a12a2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 569851672 1250 569850422 569850467
    0xa0b090303090a0308040f080102031902161b0f0501030603080a0e061201030b0403031404030903021903171b0f060a0203070c08181e0109030b090a051009150204030b07 74
    0x1200180c400040d50f44141c80300200011b050040c100031503c002c0c060610f40f00258994100300010303c94800c8603060070740700180d0226121500105005aa5540c80d03041901c0d6013240c490070f12080017441192181489284c1940b00006032540a8043c150849070005030b8903041050000081c3c0b030f0a0741e4540c006900c004104150415040b80e0350800c0e002e14043d11000d22103151619001d82150b4001c5050000401c0d602c04110006ea40440c5074405e0b00d606556030916401a4a03480704d103124603400003440c0030114111151300d224007001038000441c128240c5100c0f0900c42c81429116006200034400079000705001443d8104c0380d8005503013024851401d81d203c01000e445d10041c40d0020350009501d040c485c040a611850200d01907810345202c0c0300703405404005000040c24403c0c21744801000c2c0505400090603a45003448013014258101007a610f810255405820080092040c11920721071003840c211104216442600c080d81e0b40107031425082c0c1c56161040d90808441c1a20b0b5190302c512 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 569852922 1250 569851672 569851687
    0x10908010b0a0b1333080f061207090c050705150606070b06031e030d0c03110711040e03040e0103141225060f0b0112020a020309011101020d050712050708060a0b090303 74
    0x2d030ba01c2c1c0f401007030b50002248000e0b20a000e9032034107008918040d03040020b80c40600c41c0c0c087c4c0f4510241c0d048502190451030a42109058504240c0070b80d200305012071402e4405241650450010320480c0d11650a13502c0c541c207040b502c090320b460300b652413075000682408500000742c03100403035640022004048403071142a40d950440303d01c0b81380f40185219003003c43d5810103010540540c40a885490406006e00c540460720b00c0164007507100041c080e01e064400c0f903210307034882d5403215692040d6141a40e42e95a19040d10501d000028030040300c40d00300391030301503a80c61800300c1e440152144000c909850813003c100c440c0711308402002c180004a0321400c42600040c500d00c40c2c504036600180011a1558034117001510721503000304882c0a8500400108056a5000c82281d00c05c29003400c10f9004c1e001511060790090103513000d000c1c006071804080c000c195800c1340028000e2041c245090005a0715a0003c564252003901c550750041d084802c1031242020006c007a01c0c110720b020341124105002c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 569854172 1250 569852922 569852939
    0x1507080c2101090e1501082a04020408010e123609040302011b0302040e0609041e0305030411010507030f1b05031b0712050a0f11130b010908010b0a0b13 67
    0x2801e0f8441c21049581e10441c41100500303020903540c60007502c9404034550301d801e02c4551070300c02040d80e19004d42c3c030b00b02c5d07201210042a1240491780801500854070740d0b4850780c50318003c01203031108800340d20413502480100e202d82e401700c6050082d9483c07106001c002c0f40c050002d8040780815401c40c1618240d540e403080340c54904000e0711a80c080e45c0049000d000306104071543e0209400503008240c010403040c07004882c0141803503007290068074501a40c1d80c8600b8447d02c480d0003000d6414941003030140c088140340c0d0280203140604d00554031550b140c10243e006442c148036141c4024081600b0f50203241580b805007a4038840460000e8058032040f010f070740c2d083c1c25540560000b140c4140920b05000b00c0c00c20800c519809451207a0740740c181d904e500d443d9143d80b803900c212b0041c05040b180048508100110f00a0051b08001500340b1039080b0410403650050074403e000180014a04140040c3c1080140503440005030701802c0c01490303030700342654800c05600990b41e6518668000d0300000c0d0308113 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 569855422 1250 569854172 569854237
    0x200315190512161202011403070203070c0b040303021005012105100c090e09161e0f060e01030f0b01050a03020903160303050c1605060340051507080c 66
    0x41c031050280c03507003c8188101c00100121901300349502840c4191100050341c10210f8410f20002050202e62a96141e070702c102d03c0d612444000034083c801500c40042d40b000c54102070000d0b00d2080c1c00b41d90300005402c0510046800c00d1150040030703070b500c4d01c2030141c250f80c880c40207011900038003d03500b120014041d01e200380c4403542d100300005807441e07c040100c00403140625801c50312603005400d65090100d52581d603180580110b0b016403554910030700121459441500080102c00b1b03005545645d07403000900410a040d0320603000c2420b256900001400c0b03480b4144111405031942803d08020050131402500540865034151149510b15101450014260300c01584070360760b51503a4594600000b420086840303081d0441041c0c00406200e1603413043c00313496000000007900030f11030301b084840c1c1400e00003010001d545490380e600c0402504c02503581002415020340c0440f81501c8144e84129180c80341114201300080c85040854040000700000f0525010111501044002e000d0389c8085401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 569856672 1250 569855422 569855449
    0x210020310050a080c061b1011030a1808040614090409140f0105011a09031c0306060e0f09010608041a0f04060b030a020f13060807092003151905 64
    0x924107a001c00c0203250030400c03040034003400c401070310350300c10400042810350007000100c2c401c3c0048404000c9601c4020005500186080d940a02c214508941d1200d540e40c01520483e5542c3d003040c120515070741d055800d00c00c080d0341c0980c5d03040c03410b460190202c4200154510185061004212516130f95417180200c81109010b0080b808001050343d0185240403540e142007030650741044010011501d4200344282d400c11804107503659150f46100007410a621450062907441c100e03031400031f51541c0350703010f2000c0c2c607001e8580354420742d4208100a241e488881d901548081c80c0300c0140300c024400d00e0b226420610030480c0c0c10402009034038000710a1710854614030130401040421060001c03d0180340d4500310294040c1030302014503000b06900d4618031000f02d0140740d1622000070962180d902c14001026a01c0590360140d0300c0700c000c240900000c03e40d8045580558803d24001a215402c50b4007441e11f00c008002288004014401040503801135130300e003d0003014001a9a031100340c8100c450303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 569857922 1250 569856672 569856691
    0x1c0f21020a390b0a08130c050f01030b09042103150b0d090f0503120c0309060402120c040c050d0507031404120c020a260c030c06071407030312060506091e0102100203 73
    0xca1304107071401007500c1001043d00e1000a900c5602c00080351060303511038152034060700d0070382d0081a51001a0b018104074240301c0d400019003410071050005e01c02c1c80080290b0f0114010030001210b400031001d490302d512b9000c819884018041000301e106600820004591500201c3d101e425a01e80c0c140d809050a002e41c0c1a810000f10258900170f40e002f116408201c1605d00d90550818007085543e1340740013040240101886908440751900c10481340b041038100a00034030509110300c0000f0b0180e00500c412010b994105008906003600902441c40c40c820300340610038490b5550380b681027860015565440078805041d16460241e2515a440b41c05083d078280c0140300900302d15910705a501310350015003010742000120812940d8007080102c1000d204444141e124a442d040400f00440405400c107140e00c20341e4800010140c019015148c050903484082180c15520b100340700c0188079240589503c03104001d161846240030444000c042d0006204551107800b03100c0e960001c80e401560240308 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 569859172 1250 569857922 569857927
    0x70801090308010e0703061211150c01061d0f0c1605030412150501051c11040204030f02030709090f020411191d0d0b061c0f21020a390b 60
    0x84510f80c41c900c1e41220051804115162500090703600010301c01d00c004001416021601d4840da81d14850344041180340c40c0ac0703607911903038881c0850003450544580c056158a19000d14064080010003a10502d50000b809500c0c0c0d42d0780c2c4100341681d211948601040c4d5006e0300480100d00704001810243c900002e880c0720b00722030f60920b641c0e91490080c901980c1070030032005010381d49400e6060040100301c851000301c4014070346000d884802001040036000b030f1010400005000d405107407820264000d60a603040ba0740c580c01c0711016120074034000340c4a4080b8800d543c0040c10160b000c0e6494095104a031410b014207406003003142d002003a8004000348041d8480c1a54541c001d0484012500403950088480e01aa481e599069002071409201d0070080e4404c410540506041e422256804170b8200d405600e00c3c43c104103d8111500300484900c5103807481d01c0480c0c000030300281c42540010340b100300140c0032200d81982038403d454800c0048614108040310100251245001d0024164403a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 569860422 1250 569859172 569859179
    0x18022104032a050c131103040c090509030703022a1c05100621050a05060a05040b072f01060f030f060b060405011707020c0d110414070504140307080109030801 70
    0x310b0410b0261007400a020005000009034000a880c80542d2003680c003a541040350a00d500000c15200b0383c02d1320700b00c4001041204105035480000150b9551a10401481d19038804084d075034040c091004016034092800c40d540070080b904034184c080b00c0b400a91401085036000f0034003080c007065004044c543c6040c0100e0400000384a411003c901805007003002e1454002c400700317010141910b070b1640d844a8981c150501a007030216140c81a000801c2301c40d2414840034417401050100c400350b0700c14207041d004c00d981d144039400901801c50031800310b81d04030102032110b60b1580c2c0920040c2d0515035031480b000408a030800301140095000724042c920807a000d007044004d44107518441d9100d00030030800bc0c8038507a0404a0942480701003507001e0002d039202c44090b40352000d40c26405030b200f252a0662401c00000c04039003000700000381c070103000c041148086241201415140180402c00c180300038080050301d44800f40007920014100e030503581e03544041d02d0031924008819000181c5a00050 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 569861672 1250 569860422 569860457
    0x20d06030f14010c0c0305090d080301060906020f060f01051c0b150406140d0f05030904060311041b0918230702060c0304150b270709050103061802210403 68
    0x8040c803040301e8020b0021454012000708100c428170002005c1c45004518411117455049034011502c0d441910240d483d619020007800c02100d0340b190340e00500c107650b841881740d200403500c1c900a400b02407020410340d081c9010007403448080020060307240c41d120100c06c00b04003004030345070040c40384030500c0e00c40a03421000d00046d6030b040e400c00500c1140501c5101151b40718041d09201c540d030080b240c0720100380395203000707070540c03141c0d0000641c01420075070044284048441881c1041c031046900b0400c4410941d481c0c0c000d1014000b4000106d86225010044e14100302d400c0341e4140c0002400003001801a480b541d040030503550003400c1d129035a030800c00b5107501040410f4000301d410380c40504514255880e2152144503240c00c442c081d840701e0112946844080b0312008610349200d00f40345840080a148280c22001c440e5003000a404000014065010b0720031403040d01c202000b403210f00c041c0c03034070f40c20040c0d8456015280102200181c0e10740ca8424142c0d501e000318400d5540d801c200350301c100740 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 569862922 1250 569861672 569861693
    0x90f06080f0c09130f03090e0f100621050c040819051b18070f09051005070803062403060307150503061207080111040503121207050d020d06030f 64
    0x80126076019000c0340c1c99a03000040c004404600841c0c005030182e541c8405203100c00c00881c0f0041240c83d46040c038808164000b001e420a0b13440481a02d4a19552803100030030300302c0107844800580c0401c000501488e8402e41c1c16058200b00310a2002030120f502170f0b620200c0e00304840200803424007140c18071400000f813001455250134201d0301c1203082d8041d19516220b01a241400310340c14042030208805403112814a0001a00d207010710070580790400001e0310110003404810005400d401010a0034a0304251420001d00e0994074113050134115561540203501c040d204545c03103000e003503500c3c840481012001c0141005056000d1f16418107005040c50b147c1c268200d5030082d00b43c058a0407000383e1200a40e0f80c8904110340314104c040d00c6017561414119140c010300165400c207480c98000c500310000503c1150419400c803000794600c98041c45150040340b0b200880004900e01040c0c403d40325801800d003007040313a00f00620700310b90500000304480079980102d4412074400400814031400b07014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 569864172 1250 569862922 569862929
    0x50708030403030f03050a1d0d0329130b060403050d0305060108040201140d090602030c311701060b130305010c08040b07050c15040c15050c061915090f06 68
    0xe5081c0390850358090301c4820039500180405035100c00041c060030440c1c104003840300e0940481142c0b0303d40d940b5490380341c4001344805c0d40401e050446c125007142000003540c0b019401490200d0018034401d04010080c65052401c42d0b503142c4445011001d9034400c2c0007400114840c100500840900b0301014003030310001004d0320f050005040030000542d0304004198050b800015441742da0b010030540c82402000301d003402500c078500c04400c100210030241c008040341c40e403800c5100c122480e103031900450074188076482c0c20910b400079030402c950f00c4285100c0640303250400c00424040e1b12010207041c036030042c4036075050002d0503400410611200f03215020341151a4588501203280548510110400181901d0104000002c040007243c0050141c039440001c20140c10300c080c2414140a12180c034540141d072440c0340c48155454000d4001d408070388206100c1404be00c51551001032642c080b40390100c880d40f41a884000300c1412040c0c005414000c1c0c9404180000e400707188444940499410b0b40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 569865422 1250 569864172 569864189
    0x714030f060910181b05030f010e030711030f030a02010204060806030615120a0209010308090906011d0f150c1609090206070b04030903080a030546270507 68
    0x10184802e02401062559506034621004110b6803140e10501e0480c0304840809024045421a1803090b4621002000700301e40d011411a88500002052203080b11310742059011254420415440040c0301c001000d440024000d0507158044282c82265040d60300c44e502d1000180d41c00241400b04981181e66940c01c201705a0041c192031030306200b1003100d451030041c89486801c010350384031300100c3e0030401d00030301c943d025003400e005582d00c2c40d00b4266500b00089640c40b801c42d010026410754403806009010308240175071164201011001d100300a902411415004032111101c600c0728842d0070024480f042d0810024031000f5107008050204003a00e8000011a40c10040140c0240c1e4514040d1105c5641256040050740c8403450f0580d00c0d05460380c0002d10012001c950344091580503803109105904000080e5640041e580e022030f500556414103120104022000100502d240b40a104004c082d150001075803038081c0d0020503400100b03811103285041d522150504000701406010010660315 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 569866672 1250 569865422 569865433
    0x403050d061406030a0509030f1605070e070917010f05040308091b0102030a05310905010f050d0308040312051014030a031709011b0806012d05070309080714030f 71
    0x15000601c03c0d2102030b20002a29032030b44045000090b0901c21610050346c1c6c25043c2c0d03612a640850700c0d03960849550181c0d0940680b10f800541c00c0300035038107107108202036540d03042d030982044070f00c19907500803940b141c515642e00d21002c100c481e150300c0b949002d81d010391982042480c07c03035401450034102c020f481c1504d000c6498585241d0740c0020684208024038144541c0350003140c00c04003880c4030142c0d10b03175491040c15030300103c540c0305280f003003400c3e50382e82c0310305100580c2c03906402015500380307102d690340016515500502080c424030179541c0117841b0b40341c10640240000c042c002610b00980b81404038800010080002c1008440414054442500a4864044940c6014007000d045081c01030100c107940f00040c001d10805e60001c4000c1000e540051200c003018100200342010860b9041e0220350308000600c82440040043c0301c0c0c080d950341d103c0f00d40d884014011681e6400c02c00c000c6040c031014034804a5552070500080001d400c0c40e41180c003041290008052030b0042090708a50326030040d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 569867922 1250 569866672 569866709
    0x270b0f090c0a030e0307030c051501060e010809031b07090b030f0307030e011403042402121501230a140408070e06131b0306050f0306190204030b0403050d06 69
    0x245030005601102001c0401d80302e100c508001d4001d00710001400620740070000d2040708240d01305014080f1140108201c40603400394500380c8200a900380208004150401c440303102c030b980700701274442e482024001a87d0400f8903010351090789161300116108660080307181440700c04800d118040440c8800c40050100f00c2d2050341e1142c80c0d2085040180400003014180d6000c0d90151a02c95110801000c140d9038070302d07003070070200b501210000c030743d5440240c00c401646140ca40341c000e881c01d04005041e80c0626880d10244c0041100c0c60030982030501800180020800364803001d2919403840700440150388943c0483c000b00003200c0e80d010b00e840070b9000c0c08240b09904002403d5419101181040480f5480d02000102803580c6480f88860260a1030880c014006d000409001101a141c82c240600c0d83c0324402c10140084201c0146c2d05507000e04c00144850150050301c40031a120404010f14045c0c517920b9400881d20700310707001d80c089540054504040303501445000000c0a00806900c4050300c03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 569869172 1250 569867922 569867929
    0x1050901020f0d0e0c1906080606090907030e2109030607090e0403140d18140607120504060b0603010f240504031218060e03060108160618270b0f 64
    0x222900310010f1550b800702194541c82c100034a0100c20780041451a4044443c04800d001e44c100380036500000300080040b039414101141501c01e07050008140c44180c0d504c1c0c0c081140107003500d81c8404038030301c00c030f0703a03510211011080e8601440803200c8109030341c0c141800515240c00806084070080019064081144c0000380382c02e9900f02d40d1518100803a001c040d11000a0780c0901844c3c02c540b02e103021103080c0450300c00c0000a120700d120b951025114102200125120201102c200000ca50400100c03840d50030213030311007a8400d105540001d5080c280c8000325001e60000d07000011083d9818600303101000d482030b00c3c00b14042c4421180206040c100d08000e0a50059100c0240303000740f01c840364041c4501030a0b00b60386078032000e00349610195403070394020300d1072844504060290141200100300c8400c041002c09060501e0612040450f03d402c20031034401d0b0000481c030701c0aa40b11000401c12814594038550605c000398612a45601419410b2003101c00703035080d80e442180c56840d00c0d50b5584 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 569870422 1250 569869172 569869177
    0x60e031303080c030424030c08071b080f1207080a0c0f0c0206120f2e050607051507021006060513090e0f01020c3004092c010e01050901020f 62
    0x2640b003510076072070300722410440c1e00d10b008640016903101c95424050203140c040c0b96055055200300d40d014840030200800030f540e4110305503a030f400060001000c07484c0b01c0786030340c142c030161320b2203101d9140c031b040068014008990002000d800c812035000c014429201d50014000780c000101680400c164a80000042c200a8240e20f000061044010020b070540d61184140d440e0008043c4021145181c04d9142d440502d504030b680254010504407002c06450041c4100881c003d410000144501c0c101020409250007880044900d485649500200c012550a80074021038458006190036550103215030203441d503039041202042006c0c8400c0d0190810585010100c4040000c00a06e40200078400d41c2812211300c1305410943c000120305030b00003c0090501d08c0000d49600c1c0244111302400c1c1044404201250311f80302003c140028015484154401c0c012260ba00c1e0719a20144945520080c0300d0b0f901d40c6644890303940d500300041c210034080c01095488000203000714079100071403004030309a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 569871672 1250 569870422 569870429
    0xc030a060b042d08100c140c12090f100e0310020c060f09070902070c0f0801020f030408090103020714061b190e06040801050f150312030a0c090510020109060e0313 72
    0xc4682c40000d0110343c4091010000d08091401d851003007001d65014009031150721303100c50015061031058a8080b00078410380f240d0000c0b0303c018110916848800501c19000440d1a6a00c00d0b440040450796a91b0842c0c420360b4110f0f00d03101c2c0300340d0682000c04c140c20000070010072061240100b02400315904081242603011840901d1000140c4588141516000941d08554401c80c40081c81c0d4050003000c0c058101251401e00c1079419071601d0f215060300b030f4000c40c0315a04105c02d0920200d00015280c5001d8440da002c10701d0018106405502c0e082c15040700803032900465002501440740c18080c2410400c1030581c2c4d6a50a860000c07612402c076400c00b220345001b0200041c2d030045004aa40d4072040710010403445c0002d10041c20b0907185240042d00c15105d41c0c2c284e189500d178048040c2000701e0300d0580c00d07070812940c40c2183c0c0d9403640003024240078403091041003a18400070400381d442d1b08074000c3e07045a5a0002420006a150800803544040303000c12040d07006003d0035120442401440058 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 569872922 1250 569871672 569871719
    0x7210b1f11120301120f050304180b041104060804081e041508060102061306060320120109030f05031e07020c21120a020f01020301030302011a0603100302040b0f090c030a060b04 78
    0x100050a01b14144074010340d005200b0b000c0000c0000c0c5402611045040014800408110f01d4142d8020041119030784148a040d5031010f000030040d20f4050445958013500816805203018010038a080b24944000503440480c2000700b4144500c9409100000c54101241064182424480000b07540c1d0711000300300062403010b50f5014402c024094010740c009503407089038050107009002c080c0c0108808040c02500034000c41503004010390301405620707419501a140c46a0b00301140c1c20803140c690004245520000c41d1041c000d905109000c2040c6c420f100395406050042c7c0704004001504c175400000003d2030300d142c2e42020110201090031070718800c0e1001c0982e50382da071412090381044048008100d4552000c00004141134064025045ca018610040c407080742c13a4808014960100f42d0710b0400502c0300c59014070040c20545c2c814080c841c8014501441604010006104500c0c22165901c00b25400b1080c4036043c0110301516001c1c1020a05041c14075080c100810240d00c0c103c9111103c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 569874172 1250 569872922 569872949
    0xc08010f2102130f0e010914150a0f0b090a1a03070e0a2301060807082401110c040f02040e0f01030302030a2d020a050f0607210b1f11120301 62
    0x801a02e500500c0340c004d00800c18482c405055289900170b00401400303a84a600b0389000c04a40b9001042540c08110b000a0440320368407260001001404144c84101e52956540b140b108035950303031201a407040b86010004140000d078809001c030030b4014003108078029801f0f81011f101d18011070100e140d01c844100d03030003d6035041c01515065099281920304c42820707400d0300045621540f0601152203070000c0d44a00c400d0391100e80000440d42c1846248810702800040e4640c0990302c00d4081001807550a006c443c04001c0481c0094111001801d0440001ea0300080400c4600303c040490b940c030071181211035040d50300d075840194903482101c800d2020020005a420800303034004074144c40700315115000c512942150000a0350b565840402500c07184542030000308804400036545120b0b151503074a01c940200400001c0c40c00104200314000500c0c0c44649002154551a80803000184020290002c0d65a0407001506c02e043c98048a0743d0b98004270003100e1200410011281184d441159840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 569875422 1250 569874172 569874199
    0x60901020c011d090403080106021b0f0108040204060806190e010b01081324050702100c1b03030b0411070b1005150307120e0309041a0d12020708010c08010f2102 71
    0x1007038a941204403544400b4100612040c0b6506ca01f00c54103a90395a003c0f0b8038190f50000507a0751001c8540e041e40e40c40000c100b00c8142d503520802100e41c02a201600c04101c95448158090400c07908641c0c103e40e210001c6940000a44036020310404d0395030400080002c100e800c00003d0039540300910380004480503010720380802010003070415000749402201c0411240080781100030701000d681103001032080400c898000c3c41c02e44500e03440e107806a100d005140c0b6615020600100d803a0b102501407660703424041c401030f11140112007400041032090303503a85150f4a4107440d1920060004402100303044414409a1100b44a646d01d40d4210500700e03881e0b036030340b520803113058082d0300c0303900c40c0c42e401c0c5024950700d0040040070f0200d1032421a024010310707141e1003440007002030051403168007501490324130012400344048580c410202c2c1c070507100c03019160345e015800d49a0f4001540d001807021350040141c0e540b407081400141205804040c03194503502e4640030104089000a84580c04c20b40085 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 569876672 1250 569875422 569875457
    0xe10060f050f040e0106080a0b0108040b0c0915040602010501060809070b1303050d0305010e1303023705152412011805061608060d11010c06020d051005060901020c01 73
    0x1501056002542c45503115103405411035403400038401c49001c07814140c0404d50543c03d9011f4009014010303512a0034542e22038890402d155400307000420540c808100604040e00c60107010341030312032048901d964a602d466402400c40c1e0301640080d041042003014000c00702c0300803850100b2648400345c0c29071a6140e0850780a242582130b071004146209a81e0206165501500104c0c121f80d400c02c540c0089540780090481c42d8000541c00400582041125100e06941c0c843d06d001b860041400a4003440c002a21603201d04230305040544541c0c4c407010314202e18000c0c982c0d109a214003001030901c0071000c4a16001d820103140c1c11500d01c2101c507040001d0301c180003548904208000e400e070b1011601002e050158558100341c43c110045030b0b002e180208101c0c001d0310080d009881c05000070740b03501c1c0191101907030396440e4030b103140c10425022400c0021900e0707070010b40003d2407a02800900ca007002c800302d08001c60254801401400180015101a0f03004500d040b0a032400703003411010301d00c003116203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 569877922 1250 569876672 569876677
    0x302190c05031c0e100e0304090f02040302030a050f0d0c080405060a140f0403020111060f0408031e070f03051609090e191101080a0213030f080c0d0809070e10060f05 73
    0x35400391110f945011003411401c3c1d00140300b00903242c1c1c01d841d101103402480c0030982d01648a03821166208010810003410251b100840018039031400500b402e0700c0c0e9000904000d100901900c00743e202a2481c3d500340000d11018101c4800b40c10002e0440486a440100c00d004901c80c05100d02030200300d40721f03040e00813034142d529a40c02c050075030303035840909002c0c254035000350209a0003c0c010440c1e00103944c0c0005800b5004800045000490741c2c1d60740d99440080c0e100510510309840c1d00010b6050340b4802e00e00d0b15004098940301c440c0310040440e001000c81c0c070024100c0180030050301411184c2c58200b007a050a90364120004034a500780105c2c107030f2414480041283c204910320400a050000a000304c2056182c26a940034240c0c864488400c144e0042d0901c21032017170418801000040d80f21401900ca982c803034110b140c00d200c1c00c100302605011407106081d0100d503540341004003085062000300007400c070b00100e44001b420000089641450035000f04000c1c030000c21554036140f0301400c00e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 569879172 1250 569877922 569877937
    0xf2403020c0d05300a0209010207150306051005030f0609060f09250c1716080706061814060d0305221a090d03120e030c0307120302190c0503 62
    0xb290400d59142200400a5120080648621142d00303c0c981007800c00e100140d1501381e03120038552894666034150002540486051410361041400000741d2018407880c400110110b5100014030f20301d4001409074100451582c241000b000b04108174081662000303a6030080340c190f07001f620669075000442d0b10b1400007402c1c0d40d4000841001c02c01050030f070042d4090304004504158404081c448026184403090560081c00313926820540e00d00c08840c400907103401c0403a449482220b9645450f00843c940c400482039417000d8441c841446140d081c1c8040003698500e070b0fa41001843d54041900c6802c1d000a4078aa02c00c0e01c04074009800d040c868030075550b00c2c68400e217000c91080c2c820844504100c0091081c11205c036202c2d280344451a940c0e00541d400c01d0406001603140800c82d0341d0440e03d011802140b2410240d4401804240803801c001800710702d0b00400055a42d02554104480c2c900000154041010300421501d844d017100d10961710381100150800c40d8000000d03217811070030f501400c0c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 569880422 1250 569879172 569879197
    0xf110a0c062c160303080705030406140c1305060f040e091c08090606030d080c09030a05010e07141903021302090405040f140106060e06090d060903030501030c0f240302 74
    0x2070300100c40410b01d9564a0400d080c010440d2150f01840f00c0d508002081844090085400d07400080ca9590241c03000750303071261145a002074410782c09070141a131450203640016400c0030109240403411100341800c0c0c00781c401103d201d42400558805003c503482580140d0808681d1980400d001081c10810840b04100003040d0610745845200014203001d030841d1084154440c22f800718405041c042035000003c00b9540da003a0713403032f5540012200c2c190f0140000c65007601c2040314000104200780701c2c01c0c071001506030203054040d00d45401c0030030781200e0041c4540300d580c6c0c404080058a620301090030489506440b128200c3d100d507101d950090054004d070039041420071041100f080045a0b0003075180d80304400d82c14209a0440c601400c0b100103005a00118084c991240c00900d41100a001c140000a05104242d1001c0c3d0340d110a91b810761a044020a85441c01481000b4010307145d1000b40402800803d41c0d0380c94034401820343d2000b00303504102003030020305400203d0b2180d011540340040b0300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 569881672 1250 569880422 569880461
    0x9150303120a05040b011a0a030b0f031203090d020106050625061a0108010e060a0302041e060305030a08061503040f030905060316030c052a01060e0a0f0f110a0c06 72
    0x1d246080640f808541c00c85150001c0b10000c113200603001440000002460500f40c20300030110000c1d00108025246c895008200c0140005136030f5040100c0c40c2d8001c00021120b4030383c01c1001407685408a0542a00e0075a41032110501a645442050f13450080701c1c10301207040b4501c0c0e00d00504001030707448806040701d030804800e800b011301c010809510650080c1c2e201e12544e82e8503490401c9941c030a403415a404551260104054505a084280c101c54021000d03200c2d0040c14089608407a4250300c100ca81c0d4002203540a642500701500581c0b0000035500d0911001e0402e80c400780c20305c4020401094002a50205c0d004d02d440350b40c0c20302c0580800307010203560703003860041c2030080aa05000c042c0003d04024a20001d5031145090f940f40140c8440e1820100d030100300c4035040a0002c041c0c0003d00d40d40d50b4800200500c1c010b00190080c1141c400c0058a40c640b50700200c291001780d003801c801241004060284604c03640100da40b80803e91803e41060340c0549060005000c50286415040031710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 569882922 1250 569881672 569881681
    0x80307110d0e0a052b03050c03070b0a05010b0403030906110c10050d1505030309012a030c0507091a040926090109171c020102070b13020405070e0915030312 69
    0x402001d0780740901c21920b002e403080c1e030355040140300203142048000e095803a15110341c000e4120039610080a100e410403a080c0808d8040b05841c640244a0550707600710342c20207010034000e05100d6507024202c1d0f40105d9242078215103010b80341c41c0041c45100300300003a0014044002d40c050010803d1700800030502051b0b0014000010281c0d003245074024070440c50000d101307407144c4565420101b101c10103409107080903040e10041d600f044401c0b844034000c0341442249014014805900c0101500caa22012204620b03030a10a2401c802030300502c960510342102148074850030324038207184210844000c0b9500e101031170481841c84802e020b48415510320b040f2103206660340d4000c1c181112007070381c4620f207207030f620060107000003400044014241c01c40d4001101501000c1d0344000015000d0002503d1300b000e40e81c1d8480181c0088403000b040c001102c0356a0114500381c01a50f030007035a1792401c074441c1f90030310f0000741385001c003d000c104885100d14004415070f2020b10544072203040150317120305503203030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 569884172 1250 569882922 569882927
    0xe0a0b09010e0703020102070506090a09022d0909040b060303070204060e091b09070509060f0706020306010f03021e130315051b0408031c1418060603070302010c080307110d 76
    0x10940311200c09500b0101181c03402040024820100c0750141e0041001d586883c0c00d010260313000d40103441d0005069038010820760400d0000b004150602c00002281c0d0700c5c040c08608141d400301c643c3c491442403c0148040c1b5036581181107811036041080c044241d02c0f4040020301e1442020802504a400d20500040c0260205c420a08c1100d132842a0341d81c2840000f98143c00e6450b045005512096400110341018841e20103020101d1003d00031614003200340728820318030781045c1400c450140e000002c00c821075900000405000b141400e082d420258404803c07100203003100e81007500f0150108c0c00e00e43c20404415040001c680044006514030403001c181c60240a007201da290b80f2807800341004079541c61900442e000ca40c1d8103c00740d400d001071500030010310761030305082d011032a485010014265540341034450041512601058403076821507003090038a000100914401d8001c0401000941d0300710120000d03c44d0701c4000e02c0d40d40c0e50741207010745030034070204001440c0303111f4040b50b44502c68 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 569885422 1250 569884172 569884193
    0x39030610080601080d02061506040b04030807060b04050108100e102a08040323040312020d090f0f0501031119090608011406190e22050604090b0402090a0e0a 69
    0x1a00107040c0c80d15a80ca481403544c0d2001d01100070703001030740310360005545a10304c1e40c0c864800180007081649440c0d9030300068149030300250003c2d500c00c0400641c0000300001c0c0c2c40b60401043d000e4800b48050762400300d005807181c8040c5941920780e511100c440d082070000384038103800c09403511010050010b203080302d00c0610350400300c840110340c40b007806194000d0091900b940300301d03815501d1a02d1480c00001c0703101011103a0b0404244480144008400101c803400411003079a850742c0140911842500014030342d001760b500c0300200010303090b42442440b407800a0241614002e00340031408078011691000d403841040300400d5107242d500640300015030301c5040042190b040d5602c504541c0d80700c0052040c1e41348044200d5511003020400e9030040700000c03d040790340304030900301404460900404107401e2710340c0f20744043c2948061501150060824800c01d600030405850030064000079658a6826840103040a48200d00075400a80b940d01d268000030000d900302c5058901c6031219207800000e50 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 569886672 1250 569885422 569885429
    0x1309050a0b010206060d020325120b1906030302101a060f030105092d041406070809071703030c13031401090c09091110051e07050c0339030610 63
    0x50040c4e1010551703502d030460b0300a50170380d0010058442940e03480344240d00209101800282d43e2202000004c1c680ca00d0a84007168034015104c10700145880058007464200022880080b285008030600200e607000440c1c220200c080a80001d080d401205441c40214010a24680c001d01c001091640390082c034004d141210426074000302640c9440c5900c0e04104010302e01103110344080b603030012910b4148800560094015014401d012903200c030f1302424003000319811004100900700303004124404010b11002040311482c400ca100104840303d07038030391101800803c501c43e004190181c03c5c110f52108a0021984207800100c0768041060302806008046c0054409440242c030001d00c600361070051407040743d4408103c1d000d00a002040004e1180c403c001e031001c00105108120001e5002d00b0707003401741754201d207a81d912080a0f181a518250440c90624025001070b407460012920400003106501d10010707541e01c543e40620440c17040c1c414a03502c1990f240c400e01d070a02c14600754054815056 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 569887922 1250 569886672 569886677
    0x302030f0c0103110712030c030207050105040f1101020a0c090c2115050f031c031803210c050d0c02010f110c06060a12111903080307110a11061309050a0b01 69
    0x4919001c1300d0b1000500410b1006020340000d0392601414038070030b40c00303000000070343d0500600f80f03e02c03500c403a800c6480c110f400310f41c013a82d00ea400760184009880d09050b0105d00344001c0140650b03a0351400010304941c03050003125525000c0000c02e29000e101c40720031740202100c031401400088108174000e0b1a0081c112240707860310081c04511401c2c12409903500100c050010070005101082d10748500c84807808000401d07076507050400901840461400300d06000703580b02281103003c040c40812041780f204d03d00d042c5520b040b0020400940000599601c1c1c644110006810800d1480c1640504002c3c0f1040010701d21b000210a4040e02ca003000c0d00070401420101d039000d07030f900300602001c8c49660041424000c8642050800070300b840a055515010280402d240c030714201d410845050101d41080340ca281000c0b042107a903d0b400303603080c401d00704800010404000151240b100450794400d81600801d0700080941002100c080c0c84001041060703800c2040d484c051000308014215003034003500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 569889172 1250 569887922 569887931
    0x1c030f110c01052a0106060203040618060e0105130b0f0301061137061b020d0e1804061e020a0e060708090f1201110702040c0f020a03030c05040302030f0c0103 70
    0x500c10001807119450380e03060311464a0400440e84a40e440c40c60102d06400e054072600d81c49888035000c0c0a00b02c01050281c000b50349071820640040d1241e446031400710150071617044100100d5900c4660440e81410a00b000c542d40d000340c07050740c41c45540315005601c80303080024040c0c2c2000403030ac0c000c41c100e480d29030f1104e54031443d0b202c0070303a122200c1107005601ca948003c60810f0028850203000c0c0c0c2c80da00e03440007400d21080b55071640c0c203843c0804001004081d100750781d180d044e0340500c02c506400440e03150050140b80c0c1c2000294a000c0c80f2208450241d04001c00a01041400e5111680e9002c8103010601d4404c01c02802d00042d6201010000006d40c1c0d0781c50380d1410b8104102600c0c5403030340c01101903003851008024880000d500800d0a079000e00c1707224481040300f40a206140740c400702c4a401640e266414010300c4140d0384891000f401f0806101540c1842c070341c0c042028501540d1518012a66004d54181204c071401103400c00b961501810000c2c1030088000194040083c000ba2030500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 569890422 1250 569889172 569889197
    0x14060106080a021c020d230a0e0d020a060b060c0a050a05100b1c03020c28060e031005150a0e0f07030b1e01020106030b15030f0c031005061c030f 64
    0x400f68011042c00e401c803040000c2042c0c0720070403540c01130310036a8140c440000e0031541002c9050910382075400c208031944054400d001c0c980c12180540384100f582a40100395007400c15800030f544813080e840191140d540c504e51030b2410794820044480c00100725044560503152401d11541310054440e04542500c1240d00d00e5442a035180030303040e02100e006243c00c3c007048403000c1d0491a0514100c0440c21401030380002c122030f9882e0800c0030000510402c0c0d421f012014142d0200e0581c030140c100f44240207400c1211002540c00043c0e040c0009110b190101c1c0c56112455005c504820490303040ea0b228544210100d4a00d5418041e00d101e900041d844101c2070326070743e109904441440f84256009140c1340c0c0c04007940c02400010394545c40062000092296413034840d048c2c0210181c2e03441c0310324020f20804400c686820041d08100041c2c4e1005880030004210000395500420607103890b105e620f900001d241d03a600da1180a4114610300221505549107140040c44500c00702d5a04010800c682d8040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 569891672 1250 569890422 569890441
    0x4050d2d0503040507030b010f080d02010b0d03030f0b100c1a01290f0406050417070f17010f0c030606020f030a090306110c0703060e0d030e030301120f1406010608 72
    0x10301640d1800c40c00900512030010085925900c0140151070030b110703138140000055000b034005402041a07003006200070b802c0c44100c0707080010004200085a0401c0460070a6684044401070f4155042c180002c1e410210040345014029100b030582d40510151207003041d032500180721503041403060f030140c0c2c2d61796100c442d0160540828011048245803d045560880c0e4020705041c510220003440182481e82000206a590344140c1100d00045c0d80883c04010800c01c02c407088480203c101d01803c1080e04004a12409040030f1140c0042c0030404d240341c400e002c8082d030049a00014a100c207000c80100c61102601400c2148122801845040740c0320b40c1c55500401a03c03e00036190750b0b149007131072075926048040c0c07c3e2803985108948042284100d00001005194011480f490020600d0703a800002c26080104a032026001c0c14281141040580004811241501c3c0302141c842101c1103141410040c590307060308014020781a8000c840d500c0100042c540b0b0403108942c0d902c02d4a995100d051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 569892922 1250 569891672 569891717
    0xc03011103060a0f1a0f040e07232d0408030f07110a0b070206031b120a05011a0f0c03040e0a090605010909120809030903160e07030e070b07021804050d 67
    0x4444c3c3c130b202e0001500000e40d0941c1c004100b040c40307107030703d45040503240c1c042180700c88c1042d9042008101360380f1254401c5511009003124060b005500075040100038815000705104540f84007441e00c0014900d11400103099068a024003d01401ca0341c4400315400c2c940301036484140251822200e0062032025450300c4141402950039401a40e428500c1503800d004043e00f025045034090100758030008a00513004010380403008400102d80d10a0429454600c112070b41070f0003000c680f40d10b04d184000c1e80c440c84400c039800444d401440c56079909820f08614158050340d0840c0c10028020000d00c004038840d500411003540c0520002c200c0ba0340c2e1440e0783c104481101708010568814240c285181c80d004100e810b81c4200c030700c02528941000700b40060300340fa2601503185207245410000b0301c01000b1226800350b018200b03007020412480100c890030355800741449640c24140f4002900e1046464581081c0000250148480ca0074202482c1480c1c58180c8041000c0c00a58030b02005400304103042c4c0c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 569894172 1250 569892922 569892929
    0x9060608190c1209020f0d150c080108070501180b0c03130609030b0609090a0b0c0a0e10080c031005030d03020304050c1503150f060d0e0d14030708090c03011103060a0f 74
    0x102e46030f00a0300c0564003400740c072407040c00780c4c0e01102031b81c4a00070726142c0c10000310529105d001411a070b2802a0784101c129102480e104080004a01c0144480c9800140c40c206541090030f1102d09501144485080e481054000700755100000ca20031190b100008080d0408810001c0074801c00394681c981282c404c01d19220240c0914001004100c031810300c050301d00d030002c0825040d9110b040407520f560741c65000070784a00b81ca640b00080c07030900040c2d00c2084800b0075001112101f6107504007030b03c001d181c518003520301508080f000002c2078001c2020320011004100281c00c2e1003034235190002c040d0003034204407815217050007000c0e090780403840c0081c500315144000f9080c0a0131904d0300004071802c1c0c085400410382000c030a28140c505c2c0d0b80c03080042d0801c0c441d0380b00041183c01c00038904a003401c0124103002c0a00075662140001e840c1102d094a90016407490600c00035640c2910503860303ca6020405c03501540ba04401b00c0c001c59220005500ca1002500c01094131a52101c07815403006640c032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 569895422 1250 569894172 569894177
    0x15170c060301171908180402040b0a181e03210c080904061223030c070e1005060315030706260622060503060c190c03030609060608190c 60
    0xc010b200c07000c210400d0203ca40c60a03400c0711812902201c41c007003e030b03a038900190b52403400400d4084030307110980d12a03100403a06030f4080d0709082c82c095900110307000c4c0400741d406101070b034550103100e1181c204488009008000c40c001c141c4990111a980074002400301361081c0c0b04980800e9007005400c0590300c21074503540d48400b4070088946070b103500d0707800c8000c1c10303988581c86400000e2080c3d030210034400c4150082d000a034610780c8100701400f0b440c021407880305407600203000c120780f40340c0017094020807620400352544d01039881c0044070701c0c0d1034000e4019591180c00442404400215150442041e9078250210b629094031a0410b40c0c01c6403004241c002d110040424030f17a8400e070055889074020382c01400729a0030036141607400030403051510b0f283c02074a540d2842041546010001941c01640403d5028a40f0210f200c80e02900c1a07075003841020b010742d102504c01007600c13940c4050000e0075059001c2014584076407004000180980d0250034140f400a49590700045a104805103150303d43c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 569896672 1250 569895422 569895427
    0xa080f01171905100f140915370c0e01020304260321040c06093b010f0501120203010f05011b06020a030507110c030309210115170c06 59
    0xa407035410480352070003400c0701d06008030340c8440313410007035030240e03c004896020001c01c912240d4075406c804140001d103020213079405489201071070160070800c15040908140e05c2410040c00f2a244509000718801d82100c28254140002d48805c603540104d10702482c81e500c419032030040000481e6079009034011505031100281466211215040702c100c070b4007002401f43d0f428080120480d0349540d5002042a407198022010042000860725a0901070002420254029414800d0340a901c1c02c0c421075000a6241c9070801ea14480441c00c06080003514402406805685403c2c008900d42194403c0d640803880c118881b0614810030b000307581c146e03652500c07110401440c3c80011598050031042d401380e440d0139104540b0200310744e400185640c410315107000c5514102448000d00714030004501c05415001001d00e101950380100440e0401c3c0001c803560030340d44e1680460000c040c850501900c80640c030b0030205603946101d1a0300c02c400c480001e0a40f80d0f43c203040890076a20340c2000c141c01039116004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 569897922 1250 569896672 569896693
    0xb0112020901031104030507030c060309050c0d110a032d021c17040915090b010206040b1b041d0709030309030b0c0c010c0903060b06070b040803041103030a080f0117 73
    0x166406030034181c40501d0007150007519941e1661543e4000c1d00103559541000d141030042c8024140c03404010641440c0c204065441521100e0300c0302c881c1c926052290010320600414404a482c0044482000928911906a90b40752103d00c3c00b076803400395880c050171106001c00711401c1000b4046070540140c148100d400201d4440c035240c00c02c10f0001c43c0c0c181060f00d14801c51003d12405000036208240c0c0004100f45a1100da4520b1070b0658020180d160520742400001d07680822100c3d007083d40440c0c607003601d46441d1082c02c40c80244a034010306482010500140b803ca62a08400032554815145a46034403a00000c0350b84009078003001d00810104602000016a142c3c2c0842d400310248001c54140300585008900f034940100100c0e0000c1c1301c4c500d00380140415440f510141c5031044850502e0007125585000e8907010080c40685068000b100040c28400c02034000d03071210708020150303030740c0d85042403010704a035105a6000240f62038000010818154003041c051140c14140001c01c00c4950 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 569899172 1250 569897922 569897957
    0x90a0302040c03110c0c010818100b04020c030c01150b0c120304080f0a030b091f121403160b0c03130f031808210a080402060f130b0702040f0b01 64
    0x80d0b0169140400d1380e100400c1c0d002038800c00c064928900c0700380103001541e2040380010034401c0007038041c403240e501c502460141c2101c001421f00e0702030305905011070f030501e09000040c002c1c0222030704140d0310300000424992640d41036000301c0e00a00842404214141c44404188560041c0712000754160b00c000032460038403a100015551203072050303040034a0b01051100240f0582c2140c0e001a000c240c0f1491450303510310f4042d600691007880701c004c1c0c0140c0d0107405420380d4805c449204210000719800d5910061000c81401060f808607200c040782d82d00c2c00c2120414003010342c0203000303440051000010403400071000e030842e405244045529419101e03503403100c0900c5a200340c42202446610210005613a1400c9089002841c10030094011070808901a0130000102c0258501800d4108520010325400220f4150425019101561141c1403100c2102c40303442680d03800b01680d4010b000028001100c5002000b035184250740a1207242c1032614100251500c01c4801808038200000f83c608820 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 569900422 1250 569899172 569899181
    0x28020c01050c0a201804030f0c0c030206070302030909010603110f2101090606030f0207230312010b03011409041101080a060b03150f030706080103060c0324080c06090a030204 77
    0x2100c0050700c842c1d010707940d5070401c0c91311325040d0000581d1804240070b0343c81c682003c0c00301c058444a00c0c004c24915040d0390080c515031199075001c040c4200d0450034020f001e02d01501c0380c0a140c0c00b40c07100c0da0b1a041814040d50f2a00089402c0e407007a10003100100701c07580301c1c0c059419039000680550b8207100c40e80c440c601103504054184105008140080c104a0440c0d004035802050704403400a065800d0190040c1a180301c0500071600c1401005040001543d2144500302260414485081140c5056455085104103284140360001a00000c6030004100e001181252007403611188003141c44420b100b480a02203802a044c400080000c49155016900c0958080201500001c03141d445070005c0400b90016500603900866091440c150360906035070948141d10100c000302102460722400400300f50050100031b28607034481480c03200c000e0280d04802a5004009040514840719022030305201195109003280c038403600c80c00b10680e04000c001c5402252002c0c0484400da42940c00303000282 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 569901672 1250 569900422 569900437
    0x132307150309050a060c141314190e011e081b0604180207060506030a08030106120b220c050c070303110a08070f050c0405012607170328020c0105 64
    0x240d01d0302c90120002d441031080d0003030244548000a4581c41640e03009001c2521518050313100c4104202d01c03000c003861502031f5011141c481c503a5811515480022a118144440707082d0305d15481040302195400c250070319075041c0c401c032904400d01c181130400079044440d294410325034207802882144005280030000d00c54010006001d480c40d00d613940f5150b207000c803070740000b01c080c2c207502241c0302040220314080c96800103003c40041442c0b8515441e08412031106100340c00a02001d80213210b40800c040e00900780c940c0004041005051619910360344200464485090a620b000200d40005000d1001c3e14642e100800c02004800e0544d43c064801c029400c040c440d0902c0707000f60983c00150401e00800320240b0a0144103900449460b00924100813044000d02c298180f90060110604540b10008a4181d001c84400616503400f007a0f414182c09030000c01443e805401c1c18041c01400100070714000543c9a6848810a0001140241088841025030058000c01980401c661145c40a000761 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 569902922 1250 569901672 569901677
    0x11030a0b031c09080c030c03070e040f020d06060302010e180c0c030705160303120507080a0f0e0607030b010f020c090106030c050d0c180806100e15060313230715 71
    0x105281c01e42c000d4420410401c901001562a42c41401080802e21280e0b0503502c1c140c000b00008413407440000c0e1a00d29a015900180d0688400503003070052814461a803281c0161034102c5040c030a0909401520090105134085281182d900e0600d08025407901b000c21100e080070a0a40c8964150140c0e40d4400c0dc0342215910003400040089441807203000c410420068868110700d00d1403401402030480d03c1c20065400d8500420094150342007525241c2c003504450000990306071907000280106030001640107140300e09010005456095400b0801d1944241c0b1303802801d061a800c12070f070300c0090030304c1c0c035410105810040000a000f86c2041ca4510103500340242000c0a02002030300326a1402441400155600a0350740d051180700c0c1c803440980342c00070182c550f61401c4081001c1c18401031150040c504a00d030001040840249500540d04100600d034640d00d0412100d582030400e00840b060312060503c03842c208100103002c660a011101d8074000d8480d01b0724140d1040740d2124000c108106 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 569904172 1250 569902922 569902933
    0x3030e030a02040e010b1519080618070e040e0304050127051203270d020d060605030106030602180324090a0f15050a0e0c04050a02041706150411030a0b03 68
    0x103035540c0c044c000320071a20000001e449031144007003120b00420070503403220b5031074100005200e81880518800700340c205801e01107080d450300004144240d0611910321748108001c42408003543c0d100113450144001150140907500c2541001e50300c0b840355220382c1d4089400c410503611a102111194061501000d018006081d030395008680485040e408040094000107070905642c008081452006058200c0b40c0b0401b286e40d1000c1180301c1c81e0b01102900c241c04503030b0800100301c4181c1110b009031901800074030517599241b901602030f401002c00c103401a02070088142c01c5080000740591100381c81032400310207168101e04051150400b401032040e60051400e2000030a006a0086080710303c1421800340201d041c01d0003070121003001d04107011060401150401010300002c0850001c1d030101c60014040d111560a00c00038402c0354400300d400d0300d0349e4011f110ba0040215485100d0311520517041150340c010313802c000c125541e10603040400503090004c68550501540242149074000e01100e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 569905422 1250 569904172 569904193
    0x50601030e01150e04021f0519080402210115120c09090f02090a02090d0809090901051006050a20070512060c0315131e0c020a0f0803190c05030609130c03030e03 71
    0x47d9042e25183e156005c1040040c115030762080d160402d03070442e145854081d150b401d069001580103004040303080361403000342001d0344081d4001e61100424145044500030311580d2051140784004003020300b0f441c407640004c00040c405040340180010198000b0785814084590360802c1032044024000c0b00104d80d0a00442d412070700c1c0c403407500071000d02401c10240c486680b0810403c03082c1008200404c0369061505100c00500700349060003e480041c1842030f00c400110324111090020380019038101000c10b00d120a0103580812404240c0751f0541307490220304090041550384003403e44a040030038004000150300000000b07103100c801031004103501e4404944080e0071095a40e110060350200400000b41101101688614000348000e0b0000e4411101e050700c405a40031840d03d0041c150000010009128443c880d01c6001d00d4885074000700034440704103000500c280c001300d030040d000b800210040380388a000c643c0c00310350069000448070641429507604403031346010402d049816218484005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 569906672 1250 569905422 569905459
    0x61318020702090618010b0a11010612061113030213020904051f14030604020d020406050a09020a1d060a12020f07061407030207050312040812010306050601030e01150e0402 76
    0x11008415055405600c0341203900400408510107400c1c035104495800102c411800358044050458502c1c01c0ea41d5100d805055059400c070781c0d41000501e0700d52800001255079803c1c030400605580c06224208407e04083c1c1a041541c4200442c2c00030000c42510100010315095810160040720f01902504000c480303004102914025103e14001c00000031013000810311a1020303400a01a481003042561200004207817a481c001c1c00207070094021600010075500c03507400c04001064041c050480d00f03951161100000e4000074080c0700007920062040c044080c5180b1000304841c40140300314540283e2303281c1602e00250040b000500c0c10780a10150003260720200141c030800b802104040381900300d0a00001c29210f006000d00c0c00c1c1807050102d800031030000002cad01c2a0b4103c40740385c889191500c0c01c0207039890080082c00300c0c441c00402d00110420149403c42c44c007610382030300c0074802450400a4507081c1e80103690001d0390000c01c00c20820540305410606c540041c00600302c01e41c00317003055109 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 569907922 1250 569906672 569906699
    0x302150a2a020f0a0609030f020301020705060c0712090b0423041a01030e01111606060801020a17060a0513150b07080703200c0402030a0b1914031b0613 67
    0x2410103038415800c0301082d41442035841c490000e007121861113840c282030028251401c203000140c281041044441c045480075412a1030302c50308401240c0c02031a20889140d0180d004190450b0340f242c0310613040054901880481c4161210182040d0078181400702c0601828610701001c00300040343d40307100405484912401203000500a9404a5003078414000b40c00e40e141d022402ca03085c0e00d446c440b02484100725041d10401022101c0b0461a0300081c101a4090a0103400104d459403002840381e4245400c500c040c070100406215440d000d54a05081101780c10281c820103411800000b68112000d02c3c95000303890481c841d0382000200d684856000302d464025650460f9000d8000800c1c07014103400c155885c2c00e00c0f085000312155008610222600d4038003a9650301c0c052500480030030219141c54000d40c2d449000a00321251040447d406042c081889100b041d0b0341d1800c40300d1204907400d011a40a181c4500031a5410100728540188000d640c040b14101c41c442c2c611004c04207d0900c642079 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 569909172 1250 569907922 569907977
    0x405030706050c09040617030d090314120621060f0a14090709050c070c06080c2101050f0d05330c0a0e0a123005071106040302150a 58
    0x1102d0b51560144010312040310300642004011f05060b03041ca6201d114000200c0c3c80304030416070f01217110a4180390960381010140d05160f4124408503103141c041c0e070340c005420320481e0103c40541c1c07219004041e81c1da0346403003405218516080301d000220156138101c042c03604400c50000000f8145010b051402650a040d5180d40c081d420203201003050040d580512604a040703034031154078081059688424030a0b4034440d07202840309071030015100410307000c1620503811a00b80c0b51000c140083c507107407810000900885200d1201004260074038108202d01c2c880b41079000780209440140c003000314036100300c4000d40b8000001c139020f49050341202d00c82224012106003410f0703615a0380c1600007520340041120050301880807000d0400c401c00c040d0021055654101081c62095603540003046200704040a58440740541d40c0d40c0ca040b00350b03102004010381406002020309482d811000c001c4948600d10003c2d43c4455220041e880240401000703044807140390900101e40500c41e0a80c0c042040d1494 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 569910422 1250 569909172 569909191
    0x507050d11030903030a05070c0e28110d0b04050108060601120f0f1e0e03090a182c06060a0302061903020729062d01030b0307030507050a14010c0308040503070605 72
    0x1809005c0101402c0c1003002b03400c45405410b1a85020304544d814050350f0018400301401000c42d0300c0030390000364040c0e00c0090b4542103141d514a01c044605010701701d034a000c0e60240b45400c000041310304010ac0c8144c0038643c1655440300c0300c0e480f0040980608944245560706a40d1601e4208041074a4071800d260341c11006407030170242d99000c001c10221103000700084020b410400a900b5595507203648082a0303099000180e40b10103000c0c03e00001800e4106034040301e480341c4541c4482007150850314182030342e01e08040b1a6142daa00741880100901480000e400400030b0120f0350b00b545603522100380d450003c0ca001810b12689449900c945422201d0f61140c512541c003114440f00c040326503056018034299401c0c4a010050000170302c00701032400c5444009680001805003030380c402e8101100000000301252a243d8407801c02580b59030462180601c1008400d60024565000048090b046c010584500030b900d2500c0c7c41c00d482c1544010400c6900740020400b00000404034404c841c001c0301c500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 569911672 1250 569910422 569910427
    0x1101020f0a27120303051e010303021b010e13052809200306041103071a1201080708120304020d140606010e010527010c1a160507050d11030903030a05 66
    0x4800740301d02e060514a4194207002c1c09a05002c0d4080d4101d0401071141e240c6000107a542d504c1e0100462091103042d044040e006840c000800d0607800a500c44100141c03400071201e0030300040055800c069801200303900884d0b0345210848005065204a0b40200302e82401c0e103042841e0311034559103058200c181c504507a41c1e024aa0240000c01901600840d03c680384411503042d9a40001c3e55510010801089031140c0d1001100b0341d00c1c2841000000c01c01107a4542e52280142c1c05076141d900403800e500710007402240002568900043d14004590a0001504156591460200d01580000d1040e41c200741401c05032400203038601e0507400d8000068026040c10b04020f000100320b400c0e0b00642c80c1c1009424000c95100071541c180980d410707207010707280c084a1684034006a46500d110300c4083d200020199100078598401d501c5103128071000c00c1001c0098602a03000c1e42c0703034015540060405d502201003110001c0c0a031000150074910141240c1c105070000000038078580c011a104400100c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 569912922 1250 569911672 569911697
    0x32060406091811031b0f0a0c1205090a090c1e030504060624051602100f0e042007020301110409060f120503070818031603050d0908030a1101020f0a 65
    0xc000401100b001040706100c09052110b040e01503001c0034280e000c2c41c103c034244030703c01c0000b80c0c1d0480341d120b08584a82070302e540d9a840d0107405141c0030030043d9031600ca404d02e4541e0b0103100703104032000b80500800104486080c6030725800107000c2c1510342803d01c060450701030309090040d05038030710503a0300da40c011403180f4080c82c111055440310740c8400d44e00c0f15a81c0c0048101166441910141c102c1450103e031992109036203000c2007945480040d400500c4179020000441e0b00605034003100910381c46e40c058528a0005200c1180c0da0041090040d001031128081e6a0405000601c4903e0000b40041034080c0b100d207079038189500643c811072030790340c1e660003c100100300c08060300c0041090300d00c00040700c141900c0d0181c0b20f21a510300280708500c009800082c2c10031640c40300a00c02005802c80d243c26401e203443e000503058500083d5294401c00030b40741c0c01c0d40e00c20020384040d648018084c600740050301c0702c02c0c0c0c0c0c01c001d000079151075035400303001d8a5404084203001d0415000b03141e80d0350700300403070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 569914172 1250 569912922 569912939
    0x30b0411030c060f0a14210c03090307060507210507090501030b060a030b0a0e011d0f0402100e041e061707140d06060312020a02040e01063206040609 66
    0x224060814081d40101d0b1070340301d85642c0d00c404e58403075003440c4070403039507900c64440120713080c441e02e10600000000100b26032865405001701c0704203404516403030040c2502d840c03803448960b0000319001e900d960300402690000501c0d41e000143c01503650f04000070701030101240d500124120000700240165500104001c82d98002c03440c06c0200740c02e0134100701001c1c542010403081c0c824100031805040c0c946803107203d640c841004410040a880c9014090742d6102c12a03a001c07101503d040b9a440100e04011a0b00804041d034103038041c66005000403020314018105030349140c00c89040d1503200d1360b030780c0b075414241042e0504c410650305600e20001c0c189040162280c0340600e46000505540d001c00d10030720031010540e5020600030740803926560010110720301400640600e0b00f0007400260468261103540b0303000204120090720850b4180700881c2d0f030f4280c0e41d080b9202c078800c91308099240e0b01c2d000800515030315454005c10b9214010160f040713101d00490340e2a88640d018072300255186508000000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 569915422 1250 569914172 569914193
    0x3051b0609010b1804060213121101030c110a03030b28050910030804140a090c051c051e04150516030e150408090d0c1e080a0302030f07110604030b04 66
    0x10411a004484400e42004c8580c10764001040141020343c0000c00c1010800c6680e8008002c2c00100c600c03544034030242c9015a141aa0801080c1c0842d08109041484038041d84005904103050001400c0e83c02050320200c0140035071950054000c01c0e290314403924401e08201100681c0c002e9407142c100249810b01340070002c031005100d0580c5125601c02800041c0260342205c00b01c81c840016204147d900000003044040b070b031303800300f40f9007482c00e407c1d509402d4201001c0c04944152001d00300142024025001c1503032000c440c2440e0841410203c52481e080b81440a0f070040d02540c840946a80300042c00d400b250800d03200b0000c0c021801c4070024141da410f0003500c47e031503041030107130032418202d50f1342545a110203400100314000200b02e0303c14a495840d941460310340c0010f440703042e40f03030f5034400c820f6440c400683d010342902d11650003240129001803c26100c0354140d00a40c58a5103a0301000804c0d044103a08440a8178001c9045c040c50380c07440d02400195014100c0084035080c680f800000300d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 569916672 1250 569915422 569915441
    0x308040f06021b030601120c080d080a050a0908030c0a033c09030c020105030c1c060503010c0e030a1106071a1806070c0602030c040504090807030206090703080f0703051b060901 78
    0x10034128001d24413500e001c20701604540107203880301c011200030300c0c0c041c0303005c00907400c01403c070320800800b020724550040021780a540480801c0025803a190402c409079000f0b4007020703010381010008100035020303400084c0018080c5150004482c1e6110100300d481e0350004c0186140c128200780110700b401d0714801c1d00240300c52805402c010075003482e607024001c1c189016010b414000c02100107500329007002d040741d030f030b41d0150b1903201010440380d10388100a040901a5078020340c43c0860328078110b40030fa1041c00a40c0c070014001d10305011a5624141448007032a60360344c000d0030501180700001d410a04094904881803092419440d04202c00000301d00f4100003400541d1000c400c0c010307400d42080c42d030680d007504800003603030700d23a42c00c2e01c000072911071580b00c11f4206140103044828050180d0250440030f05c25403d944e0252200023196641c0c1c2818040075240c06000c002d408092461000107102c014402d0410a0500b921025660203d400b469000101500f00170100300040c00e084c89010b00700e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 569917922 1250 569916672 569916703
    0x30602070c12051507030e010905280b0105040c050415080f060405070806010e0a120516080f030a030b0f0402210604020408030a0c110d030f0806010813020603100308040f0602 77
    0x141c654584507141e0311018004c2100000301c0300400314010710300c00c0c1c20401d112102c0100a10030b44d600e5190090b40c82010300b0702006c0c22a07840750308000e441411440d4040302030700f041000c51581d0034101044000c002011301352081c05800c21000811905103e0801c462052a4803000b220303191900b0400c030359043c0101014801d514020400401c13a80045265802c12002e2078642e01c00f0011a000c00d038081e0589c1c0107006060f0b0702841082c10004002a50308101c40148025000b81d5521105195a031381044c0d200c02031a04240800544903100380d1000483e480c5c0203110f4000600b40e1808501241d008000d2043da1104101040c1c0360140e6080c9220740000c41034500710304d0145480521a101e025607543c007000c0140d015850010f00501c410103c202c0c41004014801f00c8049242c003400c0128402d00100110f211440040c046600a01400340b09442c011002c1c20584215802c01003603500052409009180c1c1c4c01d0044046000c0d24080c2c805020781608204899042820103444d01004600301c514 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 569919172 1250 569917922 569917949
    0xe060105040e040f020a03050613050c09150d170a0806030f0c03060a0f021201240c03020607210903210603021e0105040e0c040e010b0313080a0306030507030602070c 73
    0x1e03035a410910150301640010480c0da80307441c60f05c00280c0e8400654030241030b9204010a10080e2100c1040100c8224403038000c0340c2d102e032410018000c130b15400f101e03813880700c0084204401d0181050441040303218030400c11000d0100019000c0d142075000710b03201c0350000d4991400c00102c0d0a003040100070380076256008082e01e6103d000020b80c1c0d2900141054006a15000262900c3c2620780540700c0c440740101c050b12146d030b12884c25100540911030351035072128428483d40b008500503000d60b64501d0701b66026244644d41c0541c20b40d041050f04501d0b03010350a888883c074510031010710950000c2d91090b900c0b500e4080801a0610120503401c0c0b0004400b8a0030404000580d90710962201851070803500b03402030181d0100584030ba0003943d00801203510b00f41c080050b20764640c0c0c02401910461301ca0420113980310300e0f11040e1030004840c040100c00380b00060a0200751408060702c0c414080d8640840c000340c9951320b05003000c6003680101e031050b8011a0721002c2200d120001c01c081c0401a40c1c021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 569920422 1250 569919172 569919179
    0x3150c0c1221200901120216031e0f0c1416080607020d02031905071209091b0c0b0907050d0606080c0306190f090b010b090102070806060f0906030a021503010e06010504 74
    0x210f010003064400181c440c0000744800300769004046001100f81019421912140400d4544403140141c072411000111480218490460f11400b0460003001c01d0744c6c0c5045a40e1841c8084e10803da000c08156040483c3d0054140700c1c0c90708015460106800300d008400c4685040329040c50014094001c0095400c51000f09103041c0c0d00100340c4244a0030740c003002c002140c0320001641d55100f0190058076411401015014044c3c01102c2c5070111146100100001c100c1001d0380b070032070070b2541c58080001d912540c000011030343c000089500a4400001e40e901166a440007a00c10803086104880240d00c4881c00c11241e50140041c0000070b9040d4090455490003050080415804d11034062407680e59080b11186000154414440d142c0c0c40b280001d15035071a40b11540d0540c00400315180180300341ca00102d46104081555400350101811704801e004000b0100101c06000a01c0c25405102e00d86e02d800250b0346030007841229001c0b0014103603580d410000c5400481c580289031a060103000c10080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 569921672 1250 569920422 569920451
    0x412141e030a090b011e1401050f0d062103090e1506031801020412061506081504091707021c0807031103090a060201020a120603150c0c1221 62
    0xc8608511100d10960700e648040e0480020504031034058403029059001192880c0c41c0303c684512948a0300c54030806035590b4143d280702e440030050321800140140240b051588841d030203030880c071840a00205119840da00000319081c84614103600252000c5810414903811900690203003001c0800030040d4a081ca91807001c950f4444d200c54011030700007000851000a546071100100c2003200299962996081c2825003052811000d0b0f0303490381f8040300e041100d60b8500c038403021a10251500002035854030040140884c004890a408c56251030304a03000030b500554003074030003100340d01042e2111818014461034059055131400c003031443c0c01c00c5d8800b2441880a891502d541442c250152030003c040c0c490075400340b8a02103810000154021030f0050701900a04a0002a9650003004030405915902910002c0c0700103807402210f00740b10110300120340c01130240d41c0c0751820700e40e6080d03140340e40d00160441c51828220002d60703664008290181c5946c018000000c5420007440540c1c0b462201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 569922922 1250 569921672 569921707
    0x6010e03210901020708070806010e0108150a020901090519080d051608181908120702060712020115090614040b010e0108042102060a060902070b04080d09020405041214 74
    0x480071000000c40c000c0d0460f0b1003080a00c024003040820341d101c980e42e40704942d9658001f030090321300101c000b030000701d03022070001004085080320041a805a8690342c036036a00035841410070904000308940c0219154440d107050405004641c43e5002a80c2d1400d1001410928017500c81c404101c0c00f0460170340304c688c2180845000e540c001a000e6176414070b41c05080e05001c510340c14950058104c02502421810180907034088071072800a6a01d01e07800c4c5100d88640d88a48100254080024403c080100b284402003244000f407500001038245805030780c40d1420901c990020265030b0301c0b600c007840b0300e00359402c14840160007650280410188400080c04041002101ca0304015100c0000f809000c02c01c01c000384600c0710038585804540d05d20100a49581048582d086994102800014010828400c8070701403600206c01003040c2d00e03559100310a80e0301131281030300070b01c1c1c45009210140e40c4038821180600d2290320301820203282c801c00074084104113004282968000d00c115031924801101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 569924172 1250 569922922 569922973
    0x170c01020d020604151407030207050601061e081b0301120312020f030a0b01031b0f0206060f101d04020f0c10060f0504021b01090605060108010f030302070902030702010216050606010e03 82
    0x5003000b9105c440b040c504000d12080121a046448040502180036010303401070401c0ca00440584042d41e80701c1106554820b1510108071007040c5128900440c11f11900d0440d0300b00072002082d02d400c03021910140c5041d042a041a030075a6501000c010130540c2060016541d107a81c8101982410f10781c0040c4001390000030501c03140c0b81d460340d1b54070003168442c0c3e0000106a03d51900300a505090100c0206810030700001003000d4424440451020301e0705200c204030000f4010407422125035000c000300c3d824038400c801807401d91980030301103610780d1b1580007a108410480e40525105e0500c04120b40c1340040c0d4500d00e0741001d15110060180c15426170062003a601c080d203000d44c0c2c5030f554240c40c401006060180c0c0c02d940d441c040020b01040902e17000039001c1d403003d80e030301140c0d6600c0d6140c1110070b20481c800100564000c0c5400c01c40100d86401071a4854101e000040c141007400005080400582100301c9941c3c2002042180660f0040d8a480e400001540200301d103183c000083c01d80ba506251 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 569925422 1250 569924172 569924183
    0x90f0c070f03110d0315060201020f18030712060f0b01031505040b0d0209090601141203031303091d0a180b1b0403050304080304090516020604030c05010f06170c01020d020604 77
    0xc0d900d800e250007100c03c182c442041404840c414009004c000f801008100006107034111301090014020f40305000391080040c48101f001e140090482c0d0501c0b07109150007034150580154000002d158210f03000c8a07003214000c400c04180d00d08504401011290345409003414946049102e02c01400c10841d00c2c803d40e002030b0b9001800c00c1154000803016059544025880100c032000c05c03010820114000b4121180300300d54407a040c1c0c82c0c001300a422009151680840d40c800d100240d0014100e20303c10f0301c1c450003801c00110710b40c1c4454070300030544c0325000e40c0128903048034144220b0613100e200708108403400401c07804800080e90358000010314050006d219041c005101c5a145a100c0011a8003c6910004490340d8964074200a62642c11510604023154580b40c00288190703200302d56550400c1541e0301400d2180d480d0380d0140c404901000013a00c1542d41c502c2050f0303e1009600c40e450142c00003100011200c180325004501d082d035121042811500b00320641405a900040e00d26041980079 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 569926672 1250 569925422 569925443
    0x1030c081303140f0711042d18080c010b0a05060a05072003011d0d1403010302090a0f050901060f15050f030c0d0f0209090a1a04020c07080f0c090f0c07 67
    0x10103124550b006184c01c3c0300f080440025160104100c0300b0300500d075080192020301c04e90a941042540c101341e0b0340740c4450540145e1214038601c80499003c20b180345004049403040103101d489811507604040700241d4260340d26400707824686071504450000b40801c551851900340c42041c01040c40c011660001e000c1101d1140000002038644400074004001070000c11014070342603040b18a00000c90003603089401030340c6150000e6403088440c00710340521510064a16440d40c2e00348400c0fa40c00a04034505103942ea0744070001c0305203501905028040450020842904208a41e20300b10070356402113050501c07100c0c02d800c8450f0002c0a0300c0e00018401c46450f120b07910180c0010b8544201a041c030031aa1810804041c020410f0f0701514080700c1c11744004060f61b5405591008071500446a20301c0310624100c0295a850a500240002851f00c403c3d03a000b43e5458960341d03e030505049024000c0d400a9009086c1e5041c02c0f0651a4409140043d0a080781494030300d00b2001e01c5000c40150000160 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 569927922 1250 569926672 569926697
    0x30210051e030a06061101020304020d0b04240203010602010b0108220201020f0d030f0b120a060c0e1309030f050307210212130302070b04050303040e150d030201050601030c081303 79
    0x5140e80d035403600d050070501a5245020080b0748000c1c1181d00603000403501e488030084240e0014400e0301e120719405000c0ca644880b03180c8a04c801028004c0c012600320480340d203184108074440224041071101700320056265414410080e083d52040401141000781500c204405c03200c2c2c1e056211881500c0115411074050b81d400100c1c20810502035124040c85603075143c1001701d038150300c90840da01c0c040340100b101071141010400c1e01d090b030411000c003580c0a0704604000c602160f011403215880d41c1050b4000c8a0144046245540300c2e0401001d080e40d02c0c1c0c90403041c0b40c1c011030341140e45201440c01600e1441c10400c00740c0b0441c081c8030b4070103140f0303801594801d500249074119441030710103600d405c5191a148240e50441c2d229013104500601032110b000070004200400e440607260000e001d5401c00b400c1040e11505448003c1160310100d034a050ba210031a21400a1000c4d090b00990010586290110016040d9652203480e41d040090034010044058034009401340c809a052800d9a540382c0b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 569929172 1250 569927922 569927947
    0x1060c08030c0c210702091b03150f03070b041a0430080d0506101412040c0f06050417071a0a02010b0a080a03120e0c19030c0e1f03021005 61
    0x501844e0009810141403a503d4070725070740150408034401c541800c03255079106500f9405d06c41900c420300c07504034207102144400490442c04103007580040d101c01c0410912100091a2040903403001c001c0c603030700080c20301c08070701441c51014000b90501d45c0645440c0c60103074044030340c40d20582401c116509101005400b4000000c545d07000a812041141e107812646000f14003c1405030b42d42c1c0e210307420010240104600811001c81540b201102c80c0c0c0c24284008680c000d40c0343d00800c03c0b118504004400710f501440010964007511a50b50346075152030400b04440d4403980304896007a5241e00c80300d4100f240b000000843d00ba00d1311010401500c0d41e90b41d541c00d901509008024a40c060540c11010034200800294212310314000c1e80c0c0c07500008052010001251044103410714903402041ca07e010b6418440110302c0750030b155444084000f6900d0f1200070018919400005102d00c04105201c3d06150429242540c08180359000c06818690703800500d140354214582400d00002140740c103103419 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 569930422 1250 569929172 569929183
    0xb1005030c040e040c061e0e010f0212030106030203090f0c13020f130803031b0c1c021e1f0b011d030102160f02100f05030601083301020601060c08030c0c 68
    0x2e0103c800d14504152511903441d00050007281e00040c08a80c0f44014241504010540c414542d2103540700b211100d40111000208441d00006503c0360f0303510f00940d02d070040020f40c020100e5540058581c00c01a100030b05103040344428081d5944008601100385d91a1051a056204401d00051b540c80ca024651643c5004e4803050340d181c0020350b44d00007115007000c001113100d01e03511031101064441d401103c00c2d6a00071003040d5101903200348060619000540c4007400180447d0048800143c191240d2a20241142c52058055088001c89030500b0707a8010034442080c112543c1803200400403000204030b08851034020b100604910300e08000d9032000c1d13040320f50101304400c03200365001d55411f040401c07006031201203002e101e02c0002c43c0d102c03601c110004941042c465540700e1868803030b070b401159010401b424100d00d03107050b44c206078080c0903041e0712a07850400c4003552010105a410000e0304191050b4009001e114502c241400010b2040c41200d038070071440d0850b65180d40134500002e2070071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 569931672 1250 569930422 569930429
    0x206190b1201020c0a1b0f170109020901091a0108090c010e0a08030c0c0a09050108030313020105120103050c030f01051b16230606040c0807081b13180b1005030c04 72
    0x5502c0040d5028164802017012a500c82c081d41549840c0b0004603441050103a451185d002c0c0f01481c0402440a410200c1482ea90303040c4500010540c038a450700000c14141c030a91001e410603586000d20090742441d844042c24410342400c04080ba490041e59154541280b9020941000a100d0100c680da42c1c0d80300d5044060074008045903114113886040a0740c400382a0f19403442080c20200000e1004814001c481c169601e10000d5802c1d5140d0b13003401102c00c094940101c0c1449018413402c52983c3c480450f0b28025401003000703204a480380c005240c1022a405117401f04c59043c03104010b00d030300e010350700c004d16904140e440f207a40341010803012003e240c039130b40700405214001c0c00d000d60303c10504025060526010060b111141c40c1d100401c802c40310f5918218004c0f500300800525844c1c0151101070340103403000350741c80100d804c00740f4140450740401c980c017440d01d403014024001905407003880d00305260203160400c981c00d1f2440010b154a00c00400e02420000c0001c00940341200e00001d98008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 569932922 1250 569931672 569931709
    0x501170403031e020310140d0201050a050d0e03030c070b07030b0a0b0d020d05010803031909050606010e191523030103080319020d020405132d11030f0609070206190b 73
    0x59080c00d00040006030554491941401c800790080c07041f51034403003012600686e05849045c90401105001e0382c098105103034005041d0f80c0c03035100b10200d107420320003107205095082010780c0d605140c3ca480101c1d01c40141046080503e0004060096241c42d081d0070207a9881d088802d4468251110010107441240c5040305464205000040c903940004081c5010307204407814407482200d5180c8075422209014405002070340010042040780d4051186245501c0024110070100c080610f150451142140c0c000c100705801410b810320443d0b4840e03d080141e00c4502d1144000607626204038449000600000e0050b40c00080401ca0340d010440c502c0007044000c241c25915103440d501070800a42040c46001c0c050702c0344c0d2502d50071101c1e00f441060f6003807010546d569a4070000c0c00701101c0c100b1001400e900340c07680d1401d1140c107803c7c112010b50f210300c0300304044d2412071070b2034418014a6000900503105642c001c1c0103100b000c00e0b01080c00100c074602030030005003c0b0b51090000d503046c52154414440c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 569934172 1250 569932922 569932927
    0x3080904150905060102151006050702062101230306040b0901090203060f0609010b0405010f0c0203031c0b130504170a20011b02030f090f030a0605011d010501170403031e02 76
    0x55002c2c10390070040c82041300340c0943d00e50f61201c5052000030081158099012814030300203014072409072010381016800940750701d080108141801620381031548218040c082d0b100c0c01041b825503d07242803910f1480411250140586410100760744010181009020038000340010310021001d5001802035500101221442d040a03143c0c01c00c24001528018003441c00311001041000c0c2400c01c94044405c10b27500c25280401c01501140c2c20201c030081240d043c0400c01859864200680c0c1c0d0707201c500c1e0b4071100002c030014040100802e04490a984100303403170500d020040820b81e6840d442c0140c40f066243c6c195205072038181182e41c1c190000064440c00030489140b61389030700c1540281203210070b04820100032181c54000366528000c1c0c48a650b42007000300880d0215041505220212450180803110b60140c2e643e203903800c1c1d0350240c000b0070400c540c070070040c406851043e01c4030f40104002c0c01c00180303a05442c2c0004020180080000c0e040c151030341e80d032100c0000850300721800c48085440c00c54 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 569935422 1250 569934172 569934179
    0xc0a0603240b0a030e15070503040609060e07051c0506010512010e0312071d09011206020405060705253209070e0a1410084b060a0308090415 62
    0x3901ca41143c000400001d00e40340c81140d26070800645e00014915045502a0030f60381c014003220582c1c0f00034401c544d00c5842c2d014600c0001c1d520300031911140041e17000b804401e0b040c8030a002800c0c00914210541000b15181100814400b20303005054600603100095208588640503005d80300b541e241c400d542c80001044c6420450804400e40641256524041c00305c03d04000c0b100082c0e15600e40340d50218249004200c040c0804a0f4829582d1207048058107040ea518002601500210401c2d40c0e5034000114103148d511141004002960305c440c44210302c0c6040407d401c10000300d80745400840307100e5000b01101100301660340030052a0062681c1c409207040b42006000c0454254041c1c000c812030360021480c0001d604140c00c098001800940ba91504448200c807840400340ca118400007804101d190091680c849992200c421f80c2c44241d0203108201001900c4045044c9401c8034241d800148445582e842c0d40c9841183d401101d00c0f81c03603c1c03046002500600c0300205440159200c0e00000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 569936672 1250 569935422 569935439
    0x231e0115030f1a1c061404120f050a03020f1c090605181507030b060301030614010b0c1b190306050405120a0c0f11040921020c0a060324 60
    0x4a1001086076401c0c040100340d0101d010982c0c610043c0500004450344600010f400c2a008041c0058890290551065441c0e1243e4003254102e4840c1d510080080c8208001d00444003684103a1281d40e20b08a161404800350051250103403c08d01c504064000401000b58104203094a010b000386449004000c410f12020b4001400d07504c07011030b0720700e04200004c1d15102104d655141d03c0d00000c001b6103c040c241043c9449408401402c88081c5070b44e44100210b00c0c0c40310402795000e0743c4a00c6001a00003141e004204e4210300c141d0000c05d13451b604004032203c3d8000071035101c003603100e40344502c19141640000a104030240c00250501500380141c00000c0c0329484e000030b0f000e18021401d0700c010540c1e0f4895504144100980300011641c41c44c451000607800140c2c0d019440c0c003e106c0258066074130400602034071100c513005e44244140080003404080301e4201042e13203500600003007203041450310100300300740c06034400c80c0107059031000c4a600e00c40b000712004014800880400d000303251203240303a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 569937922 1250 569936672 569936699
    0x708040801050702120a02030702010806030f0307080703021b0a0b07030221180913020d050c0303070303090201300e0f010c020102041d10090b1215010513231e01 71
    0x90303c018401d21315400209890f250072a0180051076000e140b03400d205400540700e0a1020741142e4040c481c140703020f41c4840c0d0a10140100310311a01c440e82e43ca1070a401c000b407030b218102001c00080c0c1c2c0c0469070740c80c865546420010440300c64403032941d200c031040c0c1000e0f410440d0f044607800161a401c0440004810324200a121000c000710402d600d11324194103201e8400b104803400d41d1007224a41802c005841c2ca20030340d010300d6104038211140162520007003411500700031811170100341c0701c10840c02150781102c550000404d4000d00d20300c0003d42854410400c2440d1101102c000e030307585019440b07a070b60911682c05c2410414000780110090860028000c2d4000d11803c4118860160a001c0014130f0701503181c010380841c03042c04805410701c4a40c40c02404d501c1c1e0400c1d8004929032100305250014030503000300d00c50440c066211503141106201904070559100c1604078a000305050503034801004001001152241c01d0701296a0b541032003010300c2c00102c0010280c0309100000500d080c40044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 569939172 1250 569937922 569937931
    0xf011707081b04080c012003070b010302041803021f06050d080a08010f060e3d3b010e0607080c0106120203030d090318060c02210a0b0c070804080105 66
    0xe1048030a11800d0300c0b030640e0055010b084044e400a910880056200d01104c1180002403800d04040c1e041c5882080d2456104c001c0c121000061000108150b24052003501c00f201c4120201100c1c1903030316500291100a03810900c0000a100c9440703000d0700c441c9601090280501400d01692150541024802904051109400503244200100c1c0007003049003114229200c1c0d8031a10b00714003041d0204007501c941250042c0c204040030211008034806e0b1680c0c44602c49034420300c00c1d403891001038001e00d100c0c9014a40c2001c4800080c0201c00b800401c040d132201014840307a02200c0c1ca14840c012100c5107450040c1942c840307004603800060210000050200c903030038900820440d0f0fa504095122217a004001075410740013806201c1c814501da40001445910030b18024040c42e0300105036071250344540d0015000103000e200c0c1c080071828104412090080c00c080420030a43c2c42d02c54460392218840b100410802d688008900c404070540166185154054010382e1110b0b2100c510074003c1c4800c42c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 569940422 1250 569939172 569939191
    0xc010b0109050d08030a02250209070311040e100308030906010f080c010909150305010e100b06030c0304030507050a02040f05070f09241205130201110303090c0f01170708 75
    0x49010115801003412104803403001d0150311401460751901c3c003998000400000b01c8a40802460322004c82000a41a03171158031106d428004d00c2c82e005200040c00c004050f002410b141c1124200c8001c04441038404441160607a122660baa400d501e5549800c1c542c40101044008000d0210421f03010820038183c40354080e0b500401d585c0c0351841903548105580a501240c0e200600388a12141074108d40c100307242205101154650301e80d50030303085440c00c4800e40a10340041226550014040c041c850071000c040700d0f0f140c214102030058202a2101500042c280075001605400b080020300002034025002441080b2140c034803022107024103401c90310880002c0664079904449070154036043c041d40c2d4242c0341c9080c85e80d8000c14541c001c40c1c4d82c0d0300d404280104040c1c0e80d08084110301810f48200008485540b4000c0148000344c07400b02c48060100340b0360424420084c8400f000107584807070b080101c441d00042042e030001078551419070075001252121080400c1091904109214040c44c00321 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 569941672 1250 569940422 569940431
    0x40609060e10150f0216030516141305070903080f1206011809150e0907170304150309080d050a05010e0907141207210318180518070801020c01 63
    0x21095003002c4001800303100006a030300e04140c1c5850780b00e200380031164040f41c01100c460a1645100c0d80001d102544115030650010343d284002c02080c1041c10000c04010207604804010b23200090301c1807601c661284055907035540094146031090005400847c0c00181c00c3c1d03a5030b04400188032980d8041c030210f0340c40398050408540c055201d11010011640c4040202440d035080c041e01c500540401b401e08285800306102c0800d4048005000780d0052a500c0000c040c05440d080c1d5000d42401d881984c03601c150010f205c10041c03222407011503640307803129150024420280b482c2c040301d035004a48030b48100c580343c1000c0254080c526803049060b581c0207031034000c0607031783caa0b2483d42c0c45002c0c0c0034809080c03121501c051414108888061185d90301d61003a583c0064648280c01d03140e0180c0041284088110f0080702c0516030010451407608100d100500f98840c10080040480040e260640e20180c1d5250000342d0b480203081d0381c20300c540301c80e4000e40300856641d8244a0103500300c0c0f8010603040d440e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 569942922 1250 569941672 569941681
    0x10303050705190f020f0a091a100503061302030a180f0b060402090d061109090f100906030b060d0201020f0d031a0306060901030b0a020c1212102106060302040609060e 74
    0x10241124070050740414401d003285055800e01501c01580c0c00703040e40040b4031f8103020a10441500072030134002e100a0104540d103820b1820001107881c50b1000005011003081440707001d880f211340450100040100160341c0340c8913030b0200030040c007181d001030040c0401010034404003c10324501c8801c1c14007400001c9055200c440402080b8441c2030f801a90200c400b4100100040c226080ba50902683c265a80e060140001c042524408101c0380060f8110b00c004c00c001080c5014081d00010302500d171010080c4500315a100f440f0711101812280c403580f05001e120085a00c00c1011842c507030404015070340c004540b030202030040c06840301c400344140111100004641000550b103482007400510b041c4a591a41d100c4100d02d61004e0854420b441d020001c6401400007040703402800540b000501740e44400040704680c4140c005807034042010030500b020003410744041c16211005098140540c61501540351000c0207204a03403000303401a080607000618006254060b904403290a240d4a121307568 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 569944172 1250 569942922 569942953
    0x21c0c0b1909210f06180b07080c041421060603010b0d080301030b180d020a0b060d02090106200105100302100807090603050a060902030f060102010f2021010303050705 74
    0x9400b0740d5402074083c0003e0210320340da2440001400e40109651048038820342c13034102c03d48900801d4482a1000700400c00e08000c80baa4886500078406d00e0200d81030304190504d29640d01c02e0b882000428400e210000c03403140c1da0038010344400c2641078140d40025100c004420b85800c02201c18078480e502e0039000d0b00040c14240c1d00125044e600580c0c070b46c6582c1c00c5d507644140703c0c2400f41034085110642d10445a0494042210028021003030300109203452503440d010308240700080402c4e00130400d1030b41110041e105c4103001070540c0d80782d0604c6482c0750140c03840600001120103101c82a582004144150f030b071221110941601e000b035816120401ca1520b055490038030031f03544407001074800b0404001c0a4401d502c039a400c90341d004004501240c1d00d2405030203a17082030fa100c1c0c40d58200a0f00f408400e680900c50b0400c0b122035040d06114070841480355840304c2400136102140c560000038050180b00c0c500c080316541520701400d003691541c5904000b41280c00005040300c0c54411509403002851 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 569945422 1250 569944172 569944187
    0x60906100e010b030703060f06020a1118040b0414030a090f050118060c02040912170a1503030c05070503060f040b09190327180f18021c0c0b19 63
    0x245071050440c4240d19200c00d404099000901043c100346c0d4480011a407405050b00c0240245281d0717004100030101410030230074008491001d01d21030030991142d9088220482e0070a9030041d04403040e243d00c0c1c4e0707039402c00041c450007124180d0840d0100013852140070380c0218500c1c0541d6400d41600d800e01e5110001904d8010206500140c845469801001418400c92070407204500c040e0002c64407079203507600e26014030b40860901e000704030342070b1070355400c42100c09c129039000314070300818440503049582248034040d04d80009420442c2c492106001c2c440c0801c2000c00400020b81111241d00d08600020350412080d107044849507410300c0410407004c00028401040389120702c4051180506a4065a13415140c100c401082403020254000d0700c0312642c0750400811341c550307040059441903003025045803140460a5800c524180b02c501070441d001c0d0803081020340c16a0014641c2c41000b10500189070340c030300010003440815002003010444003015180a00c410303212001005ca601c0c2054800ca07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 569946672 1250 569945422 569945429
    0x20d0f0614010206040f0f0b01140f0301090c0b0f040312020303060111010504030f210c05090a3c1a1c0b030a02040f020409151715010504050403030608010e06090610 73
    0x181c1c06000401d002c6a586501b115206208802903e48031405580716000408260310203400700720340d00c0506140c0d08140c0c00610300050110020000c2c94656900c03441015107501491000d5403012450114840c854070844019541010041c1c40301130b101c0e000203640754011111180002e140d10b04140b0192014041e840c01194151611b040640d25013a04842e03c1d0101501c90b070550005107000403007803841e44030350002c0015903503030595100295000d100d160501d640c4501100c174280021070090458504000924540d41884802c91548414046442c030000740c00140360342001c085c0c0041c01015007802426560740a070100382048a41010400c212900040f019426030411100040189072581c8100d030400720000e00181055101c0c5d00c064100c5414411038078a120698505004030101000c00030600c2c0c200600810820056841a22030b140c0b042c45458061a01e03400400d04042c02908001c0140c04e1030f40080000c1070346071031040c0e5142c07025203911090303000d95804101036410700503000c0285d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 569947922 1250 569946672 569946677
    0x2340803040f0e042001050714060405061003080306040203090c0907050424050904090c1706010320030a11031207031d09160c02040603050628021813090204020d0f061401 75
    0x1d0036007041c050415524940b10f2410414104402800101ca000d125039180190400800cad15141ca4a480e526210000c1c1c5010f002c1c510f0304108200044c008411281d006106503009a01c90300c81002039413416250310004c0d640418221304009500e54001e0241c0211001120710300704281c131014846410608c2501c103800015410407545e001da08203034002035010b5100700c40003d02503a480c0f20460a60b4501d01481c402900b04000400c00d00c1000214401e4200c941030b120400c0c4204440082d554601d45c4600800c04100000001040d503402e01c003000300c008107444615512800b034940100140c0c01405c403003c186a808440010f80d00b00000d2540c800c080c0300c0e201c021045028041599025001c0c81d04903403050312160048001441402110300480403e207080514940b040c001c45200109130b110911800e1040c03092150602403011100c10300720090320003100700c8142d0010400982801c1001075085070001034610907010450340200e001203d070101c10050f85448204010081c0761081c1001d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 569949172 1250 569947922 569947943
    0x120a26010803130b0a3f0b1203030f0708070215070c022e0c050a02060403030f1b0503031605131502010605240c0304090906021209060702340803040f0e04 68
    0x11b00b41a00d41c1c61b1007840c9250300002c4c1c0700850410001500002d144100d440e49459920502060a19600211401e001000558290729211404450800f00102080204035005d00490300309030091140075910034903686c0a24031440e058001600302c180040049004501d0b41003060300e48014400b40300210000c3c60650b03407608161040c12660307000c0901e03054034980201c4140360010b0b52990010001075200740c6a550f15800030810217400c01500c500020008008624180700088000c02240d5129034650506027080a0b101130807905e5000c1d411060b50300340507220002c108160710803004440040c017940240304203500d4105010b5000c43d85003240303003418408850340184150385c2000e452800205821203080036070354126042a1140300c402520b91950029400801e00401d5222550221108000b000e84d0b04080e80000d50310180d01240904802c200e480c5d4290200800c0782e541808088400301e95070031901c41181c10b48030b900a2042d1030f05400070590004040c91151580c500c071f990009231868 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 569950422 1250 569949172 569949197
    0xa170711070e1009050f0604060e0108030a18170a060509120403060207030e0d11190501020c0112110408030415020c130e0102070b01080604020a0602120a26010803130b0a 75
    0x107504520107048483c0441000801042800640c03207404d10540091010031042e0418006110440381c09400c100d43c5041038400500101c007000044071407a10700c91500c4190081865011030410000d5000010480d100c070f4810f402c1d4140019400b0f03500d6018050400c100c1d2101c0c002199201020614801842000e0104102081d40c641c0900f031100e0190510803502e240c4440082c00000700300c00110b410401c0d50540e841c113410308121515601001115240303032641004000b075500c1908881382c3d4100302007000c107900c0d105080d4100c500d44041c2104230fa900c40340c03100d9840d80c40ea0001d001e1001c48400b50030520301e4a505c00907401c10040e6015044100402000201d000500800312200c5aa99020040c0350001a09106078900a00d040d00280001d070500744104040c52032280d01000031540000b0059100109500869907001100d0811422980400762541e284414580c96030080ba501e2034000107004030084000c2c80801d1801601d00130550702c40c240f03102540203038032003000028035002110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 569951672 1250 569950422 569950439
    0x609030201050c1213060905090609061c0204020f070203160b190219030903020906190b0c19030c0302061008060f06031603061b0309150903050c030a17071107 70
    0x401000310758409075050b040000e41300b46110740c0a07545444104192401c100100ea07030050140010b40f03030498920186003040000540c500c40042c06851240705050190480603d0107405c018072140e0251042d510707203a40c0568100c25420005090b07000740528107941c00c582d042c0c000c0400540e64214035650800507040c00110708501d003012480158070034500108007043c041502844818030950b10305020600f1031060000d040c002030300d6503002c1d07024002c03500041000d01010005a0f101801c000f82c44041c0e0b800c40e5440c124440c0e1040900405d0328102005040d80601a41100c41c060b03000c580054486401d40c5000c410b4520a60752039421039000300d04070446107803a154000030010304881094a8401100a130313040a2f900841c0c8459a5100c01c0484c440102520051204981002c01c01300e102c54617400100c1040e45450159165110354140030180603106441540000f54200c3c2d484010380580a400d0080c4103102c18800da40b03410000300f013603100d11041001001010090300202d4500f0514 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 569952922 1250 569951672 569951677
    0x9040b041403120f1e060a06030e0c1507060605010c0f0b06010309140a15110f0f130f14091e06010908030708030a18050d05030c1b1b0a060903020105 66
    0x318040380020811403076190148445a40580340d84100c81d038480c14540205c40301c40c6240b510150900208034100a900c0e03950301e055001b01c504a050100d0702c400074032481801c04214000302540320340c4c64413112260300286005041c2c2e1522400d810001d4641702e800545841d5a1400002c200d291110391520008030b0403802d040c0c2102043c14042080e00c11036403448401c0c02e440c0d00d402069841000707000180f10380980034000c3d901c5002d1007080b124464880c1c0750a00e110784001d881c0101c500240c440c14500050f812550944800c050a0503d191600701d1801d0940c180d10a007040e60180001c2e10740389152200c450341c00742c080940c18051102003020340001080004080d04c1c1401000040001c00c140141300070600c0d5132103600c40641c1c030301c5c056103180110341c019030001500030090624140007d10001704000c2e2481642850750b243d030358000481c1464803407501140b10b11130000c06d00303402540000070030100507a982000e0b007100c01540c505000000303c5520a400014085040401c01b65008000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 569954172 1250 569952922 569952953
    0x1006231e090a08120d110d023007141803010e07080708010203010e13020f03120c06090706021f180b0a0c03111b0f0703030e0109080d0e0913060f02040f0509040b04 72
    0x102c040c01c10b03103502e14900427600b00019504010000c1d02c0c0004200000c4648800c5280400140441908110400030260310b1200d01034220114002433180088200c401458010103000b0000c0c03100d185035030702041c3c840c00f80f031144d44810f2060f43d4003c603081006000f135030305a90549030215101d907100c3c4000c005a103403800090b40c0103248130255854030b480601444c988521100c0d0003903510a03034005210b19003123005160042641001c802801a41d90100300700c944409410800c61080d00c946804100030300841500c0480010162b072403408018107041c800d07206240d021030402c903d42c5414029010303258071b8450720361394190401440c00800c13200e2880421041d0318000710303003e6903004c144040c9482c01c160015008030381840c03104006580d02542d814042d04110700a8101640c14902c00f07000d4040b042c114500c54452040080e80f0109800303035500c1825004203051120f2101c2c03d009000a5100c0c1c0990b03a013a1140070390100301420000c4800b40240e80c440c00c2d0b03910513a25500d0300d1483e441c60b0032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 569955422 1250 569954172 569954201
    0x140a120e010f05090708060f060427060501030b0a0209010e0909161d071416031b2004090b0c030c1c0605091006231e090a08120d 57
    0xd4800c000344941d01c06081c0000e0b002400341091203030342d498010140c1c8180c009a00980410004810402c400381e003240d4181c502190514020302185c421070500000d0588482c0540090001d20071117400150489000e41c01804a035280c40020b14181c0c85283c0907640805c509000c01c4405080903810aa840160403098034051201000181d0031002d5645c4000341d80c0081c003100e5580ea0318400c1202e0f4010207241003072215603e00c944002c016000700907080100a28015101c0c042c140034280d1284c3c8441c0c888004001c0d203449140042150089620900c070544440407205c1382401c051040020710350f00010404140d80d581c005200071540020080032209009100f01809008003002884481c008031401240060400782485110070004007120980a481a0100202d175000b5407041c1003940041e21200c480c40018140907582e22031009692140030060721604d4401c05000040d2148042c1280c400e60480e54500c60540c0e03511449d4410302d40c08204011144030b060a6030f105100c41200310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 569956672 1250 569955422 569955431
    0x60901081008071d0109090f080a05070b16080108071d090a12050304060c09150804170301081f0c09210503030703050121030207090b030c0415060f140a12 68
    0x30301c00982041e40550061044e80b140d41008443e065150704c0c00c074090f1004000410002200d40c40c2c04100e41040074014100b10f10018041580502c19400c88129076040206070307000d400d008030b106291100203120030000034a418000316401c1e00202d08001140c0c60090f03503400c83d414000c08280c22a001074828034403072154407205d00002c1c410320321a26020b00319880c0d15440b4541804d04e0001d9494560308201000464081401004102c0c5c0d00e005400c01c0f10300d4441900d0341c545c13929103990145400e10689410011000060502c4000f03021481c0d060800d0524040b240b00700700807016160b1603001070012600541061100d94081020102d0444101d005015000314540ba4036040d43c0c021b0780c21000080d100c0c0c0061061814020b100c3e080c103041c2180d5103e0805c10381d00c1c020344460f0f80f400341803282503c1c1c5405015650f400c100c0345aa82d274004004220041c40d050160482c90000d00c114004211840030403000075006065183c900207040a90601e0302c81d0180044410350500703d40da02c44940d58 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 569957922 1250 569956672 569956679
    0x181507051b060c071a0903070b0403050d142205060612030412030f320d060509010909050d08040b060609060712020c040b030f190503070b070f0318020609010810 71
    0x4012460042401912080e9070754054144613200600c024170441c0d00c00c1400081c410084000030884200d06d400c8840c0c080c150300c96140c1102e413072080c01c00c24140d207400c0c40040f20401c01d003109914095203551100910340029162546841680810f000d0142d0700000c0010f000343c1800b00008528640300802c2d03d1030191620160f9036002c41141c001c0c0c0000e01d42e03c484850490300100ca0706030803440c2c14504450840c1403500300840404540e000400d9400c049000b0820300f0991b00909d0240c80000d00840043d0707102c0d14000000c0c907100d00e0503903c910400e2284803040340503140f5180503d401244a5885588980901072241e11048c1d0080d0450400c0101a01240440a03c00019002c990140601991701020032003070b1003004100a100b0f4110590100030140009044410041c1d00c49440810700b00f6410010b045015400c0e000c0c00101c2203e007004800f95109031240e901e0720007503c0400c0002381155061441070081a4001d4102004015803540c640c010360402da0301055000031070981c40d45 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 569959172 1250 569957922 569957977
    0x506091f0903121b030f050c030406020606040b0904020d1e08070317010f06271203081801020a17040f12050703080912040b0d11040e18150705 63
    0x10a2412000a00e04030001e10400440740ea02d40e00c643d5491a040301c1c204095204511002da0000004081c00440c54040c0009400750782910b0240e41082d0070781e9202c641d604006900d410381102c400b4403491078440e0f4907000d440c0000381903000d03580103400031080a900381c4d201c260350b59241a0382080030b0700c40c020180000700c0030303801031401d940310388e0350840010002160901a41010b8001d41103001541c03400340446136004480480740c0c644a40004001d5030a003400c0c000d420803580000003a0142075014a042c5904000303600c1c01025103008250000401c0c1c00700608034000d820000c0300040c01062410a071110a846041d0024000d01c80c0060311105c0d41e80d2584204a00341150000c00e10100b6502c040c1a000100154060000b2014100c18850510000c40724490342c0100e0390000c401107140300364601d01e5444240580c2c20300380c04903900c6071140d0001c0c40c082da00b1280c482e400c0c2a074922220f0440c41c04101e08500e12090400e6000c2c64840e8101590f481e000040c1c2c0071101c4442040c951070720390 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 569960422 1250 569959172 569959219
    0x201060f09060b1606020d1d10050402030c040c090306060b03061c0803040f061409010f0c0309110907020715030902041a03120c0a0213020a0f0206100b0a1106040c050102010c1404050609 82
    0x10407030508201d01208d41020f06010b40c80c0c181c9007955180c0f00411000d41c6010034480c2102c0c10441d0001400000944159140100b541002d48241d15108011a10000b1800158000c1ca0101d0b8010000b850604084e42c12400e07400005000c0c81040c00405d0026102c1c000e061081849030b5008540190300c1504174000703c000312946032a036034440c0b0715001006458802e91400d80e00c146014010140c141c2c07075003943c480d005001540034241410010309124030074070400c00544080d6600056000000c1c200078040c18030f803036041e8450f40c035100545543c14a69480c604003104060040c081c224101a01c10300290012181b04441e40980490300006030743d00c80300030380c82c032210a40050704c5003420607005000c01d002e03440b0601590300c40d00a00490340c41c5a40302504641500d81096620f03028960122200c0010901c440c0c62440b82a04bc04108010a451401903400c21f074000c000200e801b90303003240c940138810061046072404100900403400c3c030100810290750003401066140084819541545 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 569961672 1250 569960422 569960441
    0x2160212060a05060a03050c0609220c080604051501030c020309060408060f0606040f03151503030509031005010f03030e0d05030a170105010c020603060603150306070201060f09060b1606020d 84
    0x6070480410451404203920500d508080281c404203031440c195a00c6e2036a42941c40c0ca00d511482c4040b44003909940d8811200e001c10440740101d02a401c1c0700d40c41c1c400600039180611022840810000f40c0a041611600d44110b0300c21080c03c42004002c0c0040d40100700780000d0508600080007007520640380c10008000a0100e4001401c01d450401c2c000180030740041d082922803207007003204109030400040c2c1541034a822408907221103d00030301c001c0081c1800c0d00c8d40700e86440307010000028182c110014080000c400d409407800e80550040c5041251403d00843d2402125002d0510110b44640c9424204c10300140015145000e030713481b11840e6400800d66400050403c032561080401d00780d003010b00400c82030030060510030142d40000d08900004210038020a404400522401c000c500a054041005000c2e2080d9007003448009010300380c80d000d103000166000000091707040a6100d540112410380071102d040000c00355151170f001101c840180e828039001e010002880d4100e10806806 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 569962922 1250 569961672 569961709
    0x9032d080a18022112040503010c09081e12030c090a0e01050a030602210a020d1413020d050f010608030a030b04090c0306180b15150c0d03021602 64
    0x1445009640282100c000070001c0301c005042ca102c110440d80c10b030a1000c8100d070f044840b400340359001160020101c0c441300b43d981c15131041c02c098800e00c0040d0350085c010350f4019070080c801100c000c4001e4425414510070b141a5602034022101b0038400b151080c1d02e10b00700d00054645030040c160046426800070b9403600082e10001510001504e00708500600602e40705040c1c0000d58502000286039102521014021540000e6205041082d1002078001ea00d290f190039a0942400030700714000b9048a840c0d446680d2420400004021500030300c144a09501c02170783c1001140d5600388808003895503012580c80c8990304400804807400c0c040c40700540668001180c959048010080a8904008200b401545400303084030100d1403401219007030720f4201c50003040004a0325001c4580301d03034a800107007a1651100a1040e40700b803d0400c41c81101c000c540c4d0b0b035a04540003d4100052080d9500d100942d0301000c00b810225003e90040c054107210340d2031114840c20140c000c560a00c250020710b114 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 569964028 1106 569962922 569962997
    0x80118060b0c070f0f26030c0f060a050a060806150604050a1701060b030606030403030e01060b030c0a141305120a080c150601030c080103060903 64
    0x34076541034050380e620040e1106a0b21003007030340240481400b206000061000c1090003050503140040007500448044074070b19080ba9160071440c0b401e0380010300800102480c00d04c90307400ca564601000c1c00c42450030f52100000c403107004022045c1c543c030b030280502c40d0400015840f58000702e074107041d07aa090b0388500029081d000e180e0000381d00c403c10800100388603800325100c11040d1910300003400a00e03141d04602c005408101e40e0160000014000100443c1c86500b05103e1000070a0001800702d4644003400120342c011101c0b01e84824001a120550740c0d0300000c1e20701041020f080d601c1c01c0116112102d010740096104842c421140c030300f152205403c0034010048415031040c121a0b83e81c88034a202d9842e08003820741030f0035404464000079502d5020340650b0151660326174502442d60700f59681d2034014518502d0130f40410502210750031389041c401e81c14000c8506144804079 = true := by decide +kernel

theorem cover : BRFrame.Cov 569784172 569964028 := by
  have h0 := BRFrame.cov_init 569784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 569784172 ≤ n) (h2 : n < 569964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
