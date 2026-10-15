-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5298
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:24:30.315966+00:00
-- url     : https://prove2.me/submissions/25190787-8684-43a2-bb6f-6d54eac33b01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 952697841 ≤ n < 952877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 952699091 1250 952697841 952697873
    0x10050705040305061003200d02060a1205100801200a14190915050a1205040203010b030a060606020601050a03021f0203040909050102130e040b04110f0a030b24060f07 73
    0x2120310b1440d0603801480520818001a282d40403100d01f404a8070540c1e8030f4001c1c20041c007800c104c882024030b80c00d110f42500032050a000344032040005116000c824818280706520380341022103030750300d024641d0b403c4641c1c00030011030002460f103540e105601c02504840702e1041c107240182090030342d003015000a025801c00c410100740010400402030340e0000001c070940f5030402d052072186070010010b407107900c5440d1000307010506a96044100c00016030041c4e80c0b02c5e00180000c43e0107180d01c0c0003e808c0c9000030710125000303a80c3c0e034810b001140d41000518003414095401004082c115000188104000c5850031180b650403660b5180c0d40e0320a0042d80c006011000c01800050a5032400a0103500000380c0d0308203003c44d4448c0050440005203034580a2038100d00260b8940d25540c0f00c80d200c9241190010342c1001c900c00e201040c03503c0b01d4000d4402503020340701103565420180c2c11520340340e4213080707154524507503590311452599800d001c643c085100b00c3c0440343e4900141c907040d03445084c0500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 952700341 1250 952699091 952699093
    0x3071e0609062a0e0f0909030c030403031d011409060318030d020403150b21250602010c0c2001021e0c0a1e170a2f06030910050705040305 61
    0xc0700210f440c51414031601405041c4541d042c841c182c6030821201411858119640501d001ca202e410900f0003101c00764000107854203480c03034201d2034050185503134460307401100043d00489810380c4604025070b1a40d045d010910303105007070b45a842c000701c0303440c096802c04612800c000030200d80e445806d400c10000f5a03c0003c29691a010221140c000070b4010348411340c2c020792a0302a560104d03c1901c1540c488030401081c0c100c0c02c0240c1074025040000d00130460107070384a1a88080c4054900c4e000c0e988102c104010082c2803241403000090a4032051400328040c000107514400c0001e0025000f16402d1880410390002da83d56840100d24080c0c10310100000760500e06421029030401150038a2000800e450a02d001c40d49c0d44000820310600c1c1d090000f252211002c01c2c00100180a0812103194078201150510007aa4840e0211071f883c1042c600303041b00c0601000c80c4900700444204860010441d815415031420340c032401d07100c10781104800c2301c5580e81c500090400b400b403020344000e980c02074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 952701591 1250 952700341 952700351
    0xe0109230c0c0f0c041406102601030809100c02100305060307030c0906060e0108160806063112050a020907051b010506032a10030b030a1a060303071e060906 69
    0x528140e845104c030311a024011414103052203410b1030040c00c0c0340d004540c003034900c002e80c0710219802c903041032421052a507102105400003da40d060341d4a8a806180640324041d51151001c04110802c80d40024103014000701415140169550709924603050300c0904020a40307644900000b400d02010343c20007010f0190a000106210880d50311090035203c031912200681c803604001901c0d443c0c0120b80c658954042d84c0360320301080b0301c80c0504580110700500070a04050028020424005000c0d500d2076400842c1e8116024075031280b0070032001480103c0340f50441c40c1264460f96210b4080c110302078040c0c5113101c003081819124204a5591a42544045084210509800d4003074081030311094800d02c00c651099240d0300c9110f003402c1115180f02500004842880c0c1807050740c00c181d002007002d065540b130764101c55403010b010701815180700e1440424142508020788111036030180540380640c0c424031801000501c0c01d04c0c06280b00303006a01c492070761501c0d8603180010f40074140303008003124204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 952702841 1250 952701591 952701613
    0x80615190321030b030a061104180f050c030c0d0504020303070f0803010801060f0b040905190c050d180b040b0a0f1a090f0f1f030611040e0109230c0c 66
    0x8207800d209480010700c4589856801e4490460a0b207003101d1394540d05410079078107000000c42c26402806c0f803150301c540075401c190f0b9484401102d03040004528850b652250300f00105030b000d5105c0c407548820b11002650540c101000e5001c0380f8041c150344111120385d100081011365038100180c8a28641c0000b55030704800c814905403078075400c03e21500c3d007a98203104001c500d6005180907003082c4e40440d200c00d07007814070703240c840c20280501504400c4a0602c80e15400c1030380d000c6004a424140154907260761303600903c18a001140d4a41c0703410f0804810041d4245e0000c1e40800c40160400e420000c8203020f40c0310f888250004100b40140035413014500300c1082007400c02070b450b40a1420080390703108038507520401060b1901c9030494041101c001c10400103804200b0103c04a04a80c0034a10604643d540700e607521003c0718245540b1101c4010041002c2000c49410740241d030140100f00400d000e2408202c00016850001ea00341c04000104040082d43c0700044005980100c102201111034034080c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 952704091 1250 952702841 952702853
    0x91d25021b12010c1e0203090607060c1b051606050403021f14030906010302040c0c0f02100c0f0c05040e0a0308070c0204090819020c030c0109030b07210605010201060905010806151903 81
    0x8064445c01400386503000707003400d0300e0000c03081d1194090090034092401d4440d560310401081e441d9480d6040c4094000802141c103013611a25136114800c800503c0b401c003540c01c14500f5145942d0000742081400c000900060300c0d414026204c1200a4910061080710504262080804c444000d07002030703130101c1004241180041c03071604890003914100002061002d049885c5134039254040c0c4a00c41c5480c86c440181009110b1400700380f51031800e070a500215036141c5420301ca05a409480c403c0000c0d4050040385000d1194030f00b803801c03580007060400a0b80d40c0c09002d00d2802828802884a094594000d40d1544d0b0400802d0a60180c0010307900c8c90a000f2291100d001401c5c004014825540c444c0107500b8009000100410140c6030192070510b15900c0610b0003400410b4041048488000304046000404003551800c0914001088c50ae00b42000242100c40d03981c048802a41888010402c16601040350f0341c2002101c2001d07007aa1418002151a49821200d080162090041e00105002c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 952705341 1250 952704091 952704107
    0x60b120703020f1c0b0c0903190501050f24040b0d0b15040216081c090c080f010510140114042d060504060c03091d25021b12010c 57
    0x8401c907400ea00f2103000c01c0c148155900c4024001e607a0701d601c442c003400842c541004282c1d1100c003100c1c0300d5161102c0c10700424200113045c228880f21070419141d81007085400e0241a51002c0424030b041d00c949000317031410188280141104560004a0444c0c0d61291115080a107000502400a0354520801d182c143c00c0a1003c40300b1000310004007804000c81e00d0a802150503040700604403184101707060721252416800701c1c502c1c07070a90318815810100c0252500640700d81c6070007522194012440c00c20018146a00c1c064401e9190b40340004115035815895001300982c1c0311180c20240c0b0000c04001642d001c0c629042880342c803400410002071102c1501440742820b6020054259081e1100085030741c0b0300300c94018080842c0e0180001c0c42028800e6000d040b0290092808000c02c6607aa219596102d90010401096050307603420030808a0b910301d5800e1445800c5003a110f004080d02c40000d44441c245408111a04040e1001d08103a544014000300c1c18101c2070002c10940c7c14031900609410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 952706591 1250 952705341 952705343
    0x21213061808071401050903092b0804060206011d071d091501090603090b1506160f17030402010f0e0303220501140a080105040f0e011e0501050406140607060b120703 73
    0x1a2001c1001c090544c18011140128003080080d418880d1800030030291038a144036514014410384541105508100c001c920441d002e032071225991410400c000b42024016081400344032410002c10104280d07010301e2592140107454107a1040d121918051414100004816403041418060014446d25101e20400740c02098898041140d030b160000c0c0c00307944050364040d203035010038000200c0d00e001d155410601880d0007482e00380340c42d1020340d040d2120303141040c090320309003181c00d2404200001d0400c0343d0f43c01c40346801441d083d03246c59400202100c0c8405c01900c00c20400081200c203c0c0c0341001a940d0003400045c03544804a110410030300c85054030b03c210381c00601c418a10021002c500401c640c0e107543c040ea200c0c00f10368201000d000141460812901402d90f8580300000402000e01c520010280020345180e4580140010002680ca06801c564800c03441d08500300310038080c07400007289400040e01c4003520b0740102d09054004240c1c410744250454010000000700c80d5000c150242a6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 952707841 1250 952706591 952706603
    0x6050405092d030f0d18030807030606080f2e0303110709141b040302090403051b030c0a110f0406030b010f0e070504030f0c090c05071502121306180807 67
    0x100501c01010681405141c2c894031a04104103101d2015901030003440c0e8125000f03000300e0302c442c1c1e40088201d50000c10350107400250b00d01c003d028459070b05005910085c41d603440d00f60740c5403c10000740d100c5004003800d0091034045003000703080b802c0000150094402181410240c40c145c5c1c03800c02602d208004030b8003403914020b87c80c01003050101d51045122401c48590070000c03e943d4070341d11203480c00b01303003100c03040030042804008010b81d82c5001a602c42d9219903074280e1150b440d401a0301c14004502d40300d10040d041409a040c10301000149a020b6a4100c1d803101041c50581022071080440c000a40341c0160030440301206201241c0503450484400320009900b0320b40d25404d94554410035134142000990412041021400c04001300a40f075004111b0302481550714207124080356880c00e050f03408a5404900d02e002c0c010303000d04041d940350341e0030000d52400003d500d042110060050420100e4010038400c6d40601c6010783c400b440d0040042c200c0c041d107081609002d10380307400202e401c51310 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 952709091 1250 952707841 952707883
    0x10b061c1e18022412070528080a2901180303030b1206041a060402190305090f01090f03032a050315010e0108010b030711031c2009090402040605040509 67
    0x1013000a0000c5070754221041c5811030402601d00040c5501d01c0016000004114044c01400200c1c0301c4541d070040c0550342035400000100101c100074001201c020140c2848901d003104400030080e640c00d50b0070b14441840c2c00c0b03148803c0b03407000580380d01c0c4400c2840114485855001710825400d58012a902d900480b04020400c0030b40a5066491f0000c840040903d0300c405142203000e08015159900203000030300c0582012401ea54a00314080c1c6040e00340002074848003132003480b0341c09004100c80c03d00c0d920002d000701074a68942d410042691031001301015900c040d011492001d10486d40c141e01e544051040201101c480d0040558106071012080000101c60001c429030050300450000c05068650030916840c144050013244c00040c200400e000c1d46186900b50b0035014030060000c04460b26094560040c00c000070f138122410400b02041d14219185240040301c400070541300c00860848000c00944c1c0c40b8400708010340380941c00150464107000c144449450003003036a1001002c1000d010013 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 952710341 1250 952709091 952709119
    0x803040902030126030a211407090b0f0301150e0a0803040302010815010f030905010b19091a1e0402070f06020304060c0305072007080d080108010b061c1e1802 70
    0x80066100001310041c1c0c8200000c02500b0f02600d00012010011900380703200340c40514000c1c06480300207072200450000d510801150b40d8004403200d010b815015000390421450f14818105c502c010702406410800c0000c212441c64492600309a55490240403240160755401100e641c980007800f00b2804034a0700e03000201c2290003244402d01d0311318141e42c1c80308a030000c10b074103800400519800350b40654a400e03c06540361142199088148032101d00400c0c0350745890711081c04c813000302c0071580300031031244a00340e0259500102d0680701c400d0300b0410b10500d501d080001d0300910480500a140d4180b0750002400d000355076000d10f10650203401c043c85003440304403080301141c808a500c40d0102c3c03410000384030b076600000403401d45050710000f00c40d107040d1540c0b07004d8684119900d00100151903000180000e07802030051084592050311181e0808052003842e10031503001d51054001a9551264064404010600c82910541e0000c0800030244100d8601214100c40c40059005450a00c0186 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 952711591 1250 952710341 952710389
    0x10c1407081b04020a090b1836010305070b03090a051504140a020303030c1b01050405010203041a040209060d11040603050c0a080c1c0f1407031a06090403050c010608030409020301 79
    0x141c100c5d520780d40c441005504114402442e50000c2c1c10100341803005044a034425225403580c00046505103003208a05c44031070388000110640c2405a441000d10007004100207080003443d1420f8680d130003802e58907a6101c1c48014901400d041d4068180d10818030f604400300d09030240580124043d080c1c544049a203003034116a00c08040c41c000b50180e004000280d000c10220340a01f01c02c0c80b22070b420031100110090041d081d1740c400d03641070743c40ea5400010f000401040c3d0421300141c08441450f0f207003618150b0001205084010592406021811850b004000e00d08441e400c1040c001802004040e441c0d0900c00d0740d410714001b15602a5213064404101028002501d10a0b21001480c4203e422178a0112011703c4122500c03c9a40c001c1180390100022000d1010580c0585188000c0440b5440d41c100441070000b00c1584980f003400f141c0911040b03842c0c05406550054050a1699541030135100e2a4010144c95000200d8be01011a02281400b480c0e00118101c904512440c0220341c4501000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 952712841 1250 952711591 952711597
    0x906060a0806010e0409020d05150906010b040302040b0d021c05060a1401050d020604030506190b06031303082502100c02120d1e24170309010c1407081b0402 69
    0x344022501e8074002408540c4100094481e031140038001183c810b03220f901281d8075040411048500760040c000324804210701c0140303c3d41c0806010010f0020394984036a0800900c618000a4000c03a11920025000e4a0305044484043d501401c03810b1070550928070075003a120f0802d0122014041c1c1d1002c112443c01710b0042440c1e00ea20642841026482d00c4200b02500349006000c9802c003c0520001000c04d005001c81c078401c008072400c460740107102504140c116080110b500303214080500c18000d80702203030b4041c1c0d5001545828945507a844103d140400302c0041086034486148180c04240c005901040303103d07170800d0401c0c041c010203030301007426600e038070040081e4100f498060000006110305d58001c1485481010240607000078070b0028401507544004401c0000354000d442260500c3c1c02240c010018650b000180e030f050f04001104580320f20580c441c4904200a5081100c1400750b060498002040750008484010b503403642500c0d00c40c0c0c500000040c042042c0359401105042600071 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 952714091 1250 952712841 952712857
    0xf04030f1a1005010f051c051006020705030303010b160c0e07020c130e0613030e0402180f03070e01091505030a032609060c0a0e040f0506040f060311061e0d050105090606 75
    0x40c40d00306421324003085806e0b8102076641005002901d41403030b00c44d0038621480d03019508502d40f201015081c03ca0181c54112079510140c002e5004100410402103214107984070a050350750b24400c0e180481c00c2102150345290480801c0c4000601406a510340005040340440016a80d40146011055814040701c3c5100c5d00740049400140000e41035148141e804020144203040c54103250702c071807005c54100d0708400300143c84c0c82d03140c0040b01c0240c40c0c003151411400008400622a00f810908022a02403040c03003034009464840440100690310340a0300d0000d008054101c0d07002c1e1030142030082c9035550003d50b0200a1036440b0b0700019104008820b10311a607030280090440d5210040c00803403543c8160f1141c3c0401800d42101651965070f8040c0f4a001d0340880d002058900b8242c0401c412150120400040b45252000410007c0c01094000300203140444240d40c0b200d61403c01c0c4034008858030250050440002602c00e420022940a83d040ea141940c840800e540c0318001d01c2554850000c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 952715341 1250 952714091 952714097
    0x504090e0115270b0f0103050601022a040f0213060302211509090a0f0318080d0807020c0d0c030b04020d0b0108030408010c1103221d1605040b0a050f04030f1a100501 73
    0x1035805c04c01e50103500056080101031048500210718040321b4004808076190404d0380c9507480d0001e80342481d00c0d0007050160308440e0000c41c54109c40011001520b00e41c3c1c402e01040c90b8012034aa810341c4001e04900f411982040b100d078041d8913054100c001c3c010900f10300c40e0b1081500700082601400d0010358a000154045181002c3d42c01c01c4c0c50690f5081d03a9403803403001c00c14901d0f4011030b08080074480601902e6654a6406181c141a90042c0c10060342c40051401800c0200c2c000e008940c502080e002100d13004441d015031912640080b5080010a103800791108914600001391104000700420407103c114000b0003d89071544400c0790010000015a00154401c0c81040351a070044110042d80744412074a03400c5482c1c0e00c00d03262020741c66020400046040c4042045540d07000840810304440312031503c0d5140c04c2c1403a1425480307010b03050600003006404904808900c103540121400795810400d10205021103140000566112040b02c4a200b4407150110303008414015506090340e805071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 952716591 1250 952715341 952715359
    0x51f02031006091a0906041805040209070e030703230f2104030213020a0e03010c020d0e0306011d19110c0c0108010e0a0905010f02070c080706020a030504090e0115270b 74
    0x403a8044d0f904102d0490380e0044003008005010b074074901c4541c080500c80000071130b0368580381c0104510958020110820300100c405c4107070340350f41c022500c0000c0d42c1c2d2010341041c040c080030a0115034031038169802d0440e8890810713110800000003a10305a00042d1042c0f40741600f002c05403c8000780100d101c003d40114034001d80c3c046c08080b6802400007800546032221110900034006400e42d003d2900c0d4101680003041150300d2181d1281008a0110094004006035490a03800398002900d0300416189120081d001c00c011400380600d14208031030000c014081400354031003458040e8402604100b05202e05c1c64038190950103440c41904a913841c0ca100400303a030301c461111024101204040314255130b1000c503220b28006901c0034201490054040e0054981000016403801040343c0000c000d552000181b000020350000444003620352014011070051a080c04950140440074603402c031108042c2c00c00308001d1003000440600a100715251541e010303e0b41c620404980c03201e0401c40d00b04c030f448 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 952717841 1250 952716591 952716629
    0x11012c1207060b0f03100b0a09060e15030a081306030c08040c15020a1407030c060503040f2429011b060504110a06020d02010b040e1504051f0203100609 67
    0xb0783c45024050406841248401c0d4058002800d04e00c601d50307004089582d40b00e5000b21810140e20314806030240f40410040f03503060039054903400d5001400d0074050406d454480106840a100300318805a00c5980320341c46040c0d2201310301e00100349000c0e4400007880c003028070103480c0c4203111850007540c216074034070402401c05024000c204881e10b141070030f601c940d01040c0c0000c1d1034a042003403600a65000b82290901718a070100c41c1c041c940d44183d041200520500001c0b072000d80100d01c2142d0300c195a0181750152040340b45966102d103080d044a2031900360755044048611602044502e5585070600071014000011b44007112106148941c0300c41007030300c1400048244d0700403078006004d1548420749400c02c0000601500c03050704480d0043e00241003400c0e00540900503074410584c02c960a004518600f107485543d0f0480416000b0310f2034080020509211080c4a0710010100c900782c003101441090f50342002035481074444440c000980500000c60b07a114400c904196441884a0300011400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 952719091 1250 952717841 952717853
    0x314010f11031602120a05070b0603010b1309020a0b0c03091011070b160804030c09050f010b03160c3306030b060925080a0b03061603020a11012c1207 66
    0x51051000e40c0f0a10b400c5c21503080e1768034054940100c00d503940ca541d50456240c0741c5145c640c081c01c00e41c000c1c0c1c10300c400401269640501156140341108000804400ca800091190011580032165542e0001a40010000c01000a048c000c2050b507008007403d000b180111440201c0c0e070800c15803500002ea00784002c1900000a0801000b40d01e13441800c0c032015180d0000c00d83c81a4012184008d80030000c110146540c02026404910700b40300c000706614254030003015220040040f148000110b40480c41c0300d000f6031007524030581100303040b21521408441ca500320b411069142d0086407420407a00100f0119002c1c0c10207aa92007045110151140c00900402d060090800403d600100030035184c1031041c0060344140d049185e458244505000c40352600300d035541900540690070400400140c0c6410b1228482090004d190050f41c030340d42c103007044505918406c0c070223000b5428800c24401900502c52814511b41a0201400c0c0b01203880e15090359800c8a14403410b100750044c004c0d00c000c244 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 952720341 1250 952719091 952719121
    0x231902070201020a0b160f0206070212070501140a050a0b030c0307030210020a050105100608130c030305090103060801020f19110c0603060604031208070210020405090609150a0314010f1103 83
    0x1c0706004488440509030f46092000d0b80c104e602c040104004060025120381c01a0b44e0b00809842e40003903c43e600304220300a4590302552000c005038040001c801040150951111009820000c91740a10b41085a01c08000d01000c0d14000b013014200001c5001c10f140100398940f0592008001b444401c0c0703540d0034001560f02d040d84100031350194207d802c002c140203002b031030300c2604081811a030490410384080e01d41e0601170300050341035051003503410004030030a03102015290182440368a40c01e0000041b005041a034103c090b195002055081d08207081d4000b130207000f40d45000403407844618000031520401c000c94101070543c0325511140f810304064009540042024042924242d100d4603042d0000303801d00300d2600010403070130402c024643d041c0545525440702190a5140902c2c107000a5032141002e0401845889410007049034a030700c0c002000300303140b400f800030405159030b4102001c0c200b4200120007855400c0000590700c240c060f21500c0129002c101e052405c6888003808410102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 952721591 1250 952720341 952720343
    0x10605030706050301051c02190608070f080a111e070b0705070b0103080f13060c050f060702100b060910020304091812201609110901021c140d23190207 67
    0x42d1f6540b0790100580c403580c1c1070700c2480300503c3c5698000c030f01d4440c0041c082c0354000c0c5448200081402c0d540c0d4a144c0c000105030b004401d025011820300081c910113000c0b8425a0070039007450408401c1c03101c21401c4c4c0005416050300810204d0040c0d500d00074140c50510440d03e006142c0c413851401400040c00c0b078005001c0e040c0f001d0600505000c0880d40032400640d0715040b40022660050050042010400040a0003900f407009080e00b0f05184602959407a01d00110450154642402c0c00e22510307028103960b40c010004000081d2070005a401a44a90060240049841c28415140000080c000281c0314056101d45480d04000034500100d6a40100000815480c030030140c8206040d002000300104102403d1000c0d110303103180603081004c980680c2d2020303a40344000d020358142c60b070b00414510180303649513211000c07032110010219000700102c40366a42407800450f10001c104041e5024145038a80115801d51520803026903000b41362080340d980c80300c642d04000103900ea0656030083c0041c0303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 952722841 1250 952721591 952721629
    0x81302012c0409140c031b04110d020301090621081602010e03010536060721061503061e1403070302030106030b04031e0203040504020315130b0301060503070605030105 74
    0x2503100003001030141c2d51901001d40b0000000a46404e43d04005d20800c1800e507001c0307000b001002d5004011a07403514050711030b0b0b442256203491802460307008000311600c01200b0307002190f0702e68464071010001c1110f801805c0001c022202c85140d444c1e00d000903190b0075904900100c1c10200d10508201c85480780e007404070704000104c90340c41e2141c1c0302406158050302922007c0d240d03048903569001558080c22501080d034268030300201d424400040380e5150031040c1480c20b483c09050209902d25030850b5058002e044615000300020340701c8035510100c41c2e665960b0b9052144030b90b11540000800710404815910b031545200c1002020012040f03c0b0b004031020341985c8480b656500001d0845007503601c25103000018070204010558481150700b80211a42410035101101c3c4800035580e0080d802010300440d0b000010030002100c80c2c0c0040d4003503900628540741e140c40c1c4040740d40070307044030340c40c03a8080d40c241580490640f50200344142565041d0b070b81d841c10b5038a400201314540704200b001d2081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 952724091 1250 952722841 952722917
    0xb01050c0f0a1101031a0f0f09250507150c110a201219061d100509010c2f0102070b010e0105010201051308030612070f030308130201 59
    0x303440380c203220106041800101500000c0d005060098902541c02c54807410140380c6020070b180e4408001d80d60f400002c0c1566030801d4004040042041c035124602455480600d0b0400c00070b608004030550360b0a615014403c2d4100f0300c21000c107444c240122540140315820140485030000c01d29845224042c00d42d00e0b1050311019400101400c2c9484904240c07584101100c8602070346640480510102c4001c3c0c41e0421f17101c40d4605065280d13481ca4040e004102401c01e568414001c19400145034031940081c081301800e00420725940ea980ca04003140c1401d13040c41d0000d141800f061046820100b01502c0e1201241d80040c40c0d401c0070b1064402100b045400c0c004a40e680413400d05c0034006492240300c400300d107941055100d0145400c1680804c0c11a0704020030014028205001c209030b9070341c080030094581c0c5507400020410066070003c0440c0b485030a034002120444584002c00302d0780a600d9a030640c1c1c03038500719558105d48212001e404540744110440352160344c4c003180301d001c910072140c9102c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 952725341 1250 952724091 952724107
    0xa050301290a03020c011a0a05091e010e150a05013608030306120d0c3005180109080706140f030403020d1214010902030903041206061e0f090b0105 65
    0x6942e800540d442c0300042e50101d0200280f030024820106e60240c0400d1010014071440000b950214460040b28010005400414040e03215158040500404c00e020110a981c5aa103180e10708041200c0e0b0001801c0032522040079810000660390594406a4a204500d01601c28400c023482c200583c1404200000300d0240c1c0b0841c0100310003002e40b08a42c080e5a4030300340407040010f60203180840700300b80d0700180b541c0c1d0b0782ca94100040d218007690200b107141d4891181c50142c0300450171045480109480c4174001001a5400b500a000180c0c0c0f0345030110440e50708000440e4021041d008a44581c2d02c09982441a240686145203d8000c1510f1803172030001d06000c00171441e0000d40e4100c0150303010400802801350410120941c480c0300c280d041240809003964020003450600c06c0100041d40040410b01081c418012980908202a0380818542c50741c40d00c1070040030705200b1094004180c1d40e0755581c014101004d4000c4541180c0701e40200c0f03052250702001030448102c09814040d040003008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 952726591 1250 952725341 952725419
    0x2030613050a06060f05030c09011803080c0a02090907080c0f0301061505070507062a141605090f01081f090f030f1805010215040609020409080a0908030a050301 71
    0x60302c40c0d03940300408185a80307400d80240c02800131030060018000140108990062080261140b095092034000c640c50743c5003040385030302c2010390409400032034000303207a0100743c0f00001e08250141c82a01e4a40c00e907501c00007407984848aa000d828569000600c002c40d1510b4010307094850220014000120660f4400c1c41c036495030840803041d0007065002c540c201c21f0140030f100d90340041c07180c1c2c20148141010b044200c00e0284018003028100138000540714248000100407205102215040310000c2d1440e080718000c00c2c180b8810644650b2a80c8001040c9100ca0007200341210030a100908003a881c005214001215208000405a50320011000810307101091103c03514065194184000500100180703039880c0b80c0824505488103440410060342d000412041e403942c1d045003040c550712245003101c040c00f05402d000c1d500c076080c00b01400901155100412520b205921441c16003940c0700c811303d840740078206507080814002e000403c50190441c1c290755030b400f05c1500300008040890182 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 952727841 1250 952726591 952726601
    0x503070b090a0b0c100c050415180f080703060617120319060306020903010c030c1407080910031b020705010c0f02010509090a06090b180103170d0e0c01090519030602030613 76
    0x4100b2544503041170b000080b90340c81488040782d0180303001480e15090002c000b014103000340c01d40b002c210300398910042e1507100015040184c60401800744072030740d41d41903165480049002c181d40107407420303c0001c0c0c03076158001030910320070344d01c1c003d404251800c00006085800081900c810b581000684003134407800c0b0300c0b03000051442070000580311039000d0309040c216070341d411280b010715140182448070250011074402e49900340d40d0304250b40755500d01d0f1140c0d040c000c41703820b20f402c010814022031000b50140c110780005000000078051489198100300ea90310f41c00e1242501203240d0382159400700318000202100c060043c10194540007109011135a61038044501180075555403006002e500300900600d0326002d400c5070384106001c00c81040b0720901006201c000c00004400a0001300c00e07214000359054428001e000b003000401060342039460304a81c3d841140003c0e550728002c552890514482c0c080e03403c8440318040480d045644400003544042e002d10f078010100c807140f10403001c03a4014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 952729091 1250 952727841 952727857
    0x1020a050a120b030c0405130c030506090f030f190306051804060e0a1109060a1710050c0309031605070f0902210402090a0b270601020706090503070b090a0b 69
    0x5101c0c1e07a07000544004055041d403500868a49041c552405007a60340055a0201481c0440300080e99880e02ea103981e011814460008101c0d000c0104004144140404c00602ca556100f0a6a544140c4900000e071a80714001103421601c2c024449016050380d144040e1505113454100001d500e074540000a07250b0303002d0100703201c0550300300c0e0030842000b84a020b030002500c1010300a050600320742d0342d100624441d0007541030190f070b0140c0004034596036030a40d0b0f50080542d504030b015154452607083c0c2d10744070121070f0075020341d0404020a02c20064002101d2042c1c80c001d02442c01c10340400003400f070401107480c0c180e5007403042040c082007421600d001c0000030b1882d0000142d813512400049142c240000200c11a030350149020080543c4821080079401401c00000146007211200052895902d80c81c80c4600d50b190b842020242455040c50107000d40c030700741c0848800a641f100110303482001c6015454058204001c20041e04c1000700203429520002014401e0061311401d000d901500220030b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 952730341 1250 952729091 952729097
    0xc070b04090b0301061505160804050a031a060d1211011b03060609090209090c0c0f0a080a200706030b0103090f051f060f0b030903120403080601021006150e0a030501020a 75
    0xb601403920325003442841d000b0801880384201962411401410500915501c0c2940104801582e003c101c0c180003141d000d0403000300900401070301c9040c440079201101400031080701d00800890082d181001060542590141c2c24115004198208480885424003111219926a804905400c6030f04080100152140d07800245030340c64035200900f070001c1d80e4841d8810600c100404403042e21003c05007a03005044c0c10350390355038078040c252035840c02c200c8220b90b503104d002d0070138a2820811884018a40c0751629130b41c65030b07a072450000700c00a40340c0d0740440c19599070002c039003040450700030703042480b06440c141000201d18040341c40c0d6123101084a07030202c07100d4004003813142110154a500c010f034010204020003030103003000900c2c00c4201c594054011030400200004803420b2040003100c0b203102050b4104c5030503081a25000d41814000e496860140c0208401b40421581a10232501100e4481c0d221503001440c8a4090700e15240403151290013240c02c040c04000b0400900003003041c1103141e030b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 952731591 1250 952730341 952730351
    0xe04030e03010944030105060a0c0602040b12011d0a0c02070e0a15080616030504020d06150306050a020a020a060b06040f031a070c051c110a030806150a0f050c070b0409 74
    0x40305660b110b07509101000f500d808603610b881c04d5000b030070b02500c0c190b440641d10143d81d03d13440030f0f00b601c08440700700d4010302c15400011b0110382520660f001c3c0822200030310816806980b2101000c00c0041c103078040e142e48410401c001071072603616070000c0145441500542e8800782d19411903e141402c01c41d0012810703a2692141d10000e000190800020000b91010f480301e414004030000301404e01d48036000130583c860020606655601d000d0700e02d084e5000204010702e0101c1540c50382000394520040c1c1d180361802c0300207020948035008403013a07400c80d0340c06406181246d40d660070040c80d0b81c0e1805508031006100200d00040e403a0720b9000618040c1c0c030080e007003a01c45c50048040c11402443d040c00c0204c0010841c0010300300181e071a4a0300424040c3c002c0070311807a1000c894182044481000901c034022000050640090072070f8040c1401b5076501d16501c8114950201511520845100180c41310900010b22840740000e0414220310740e042e1005140d443c0b1001000e50025046480b800e80c0c1d41d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 952732841 1250 952731591 952731653
    0x1d0604170d0e010e1c020703031d060c0a1101090f09110c0105040c080d090b190216060513050a0b030403050703020c04022a0d0504091a03240c040e04030e030109 71
    0x1041085203c02a03400c0a4200040108009440d1f4060748401418808500fa58169914114a08a41902001d892103413a90386081c01c05944500403801500d005d03103d0040e1120300d51280b070502d000c1e02c882a406130701c2d0030b1801417204014901030011003031031501070105c0610340100b80107040c0601c1c0590000d154140c01c1c4400c0ca42400851050740040c0110820708002d80c030b00101c250b0300104039035011100403071050b91060b0f040007820780189104546900703011452a801101a100034200070b040c0e130034015160020300810306894003c070310f0503030400d00005000a2256000346000d41c03207841546c0c0750244201c041400c1ea00550042c1e184400b8814080c017a040f0603030880c01c0c0301d014181c0140b85d610782d070f0300d0040c026101c0c0b80074006000d6190461080d9010961940400320740010702115032401d05a0b04040201c1c2065a0071007007000900702081c14450f00d1380075103042e11803071043c6c0c00312a1250f9406544003130903880b8068265490704102c40124160400da8490408000c913007254840030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 952734091 1250 952732841 952732843
    0xf07031406010828060b1002010e070504021c0504080714070311040203070c031d0613050114040e06060d090b0f0609070c0f0b06150a02010902041d0604170d0e010e 72
    0x5030042c602e035500c03030f001e0100055510459a5070b464140104c070340451820f420035401410402a00316008000403281000c216415401401780082501c10b640810362100e0405c8160320070b01042c1e03080e24448280704d5800c04603c0d403050f5080303403040040e07030f141000c03590302e000385a0241500d103040c541046008200740130f01c4442c000c914060448045185180415014102214000010f41042028410f400c8214440f1002808008000b00f00c7c80d103551001094014000703039409181d00280300342422010280405042d5422b0711942c808050203669990203210b200c7c2c2084081c080b440b070300c41c002e10f000300c2d209000c2980107000c0d0314004078891502d10103114000c4006000042084542100c032000300e0720900005210550105515229481305e0000452108a580b02c0569008002500184954055103c011070500c203a070140559481c28944582c0039220500c3e00e80240c0203100090300041013110300d50007006c4081e035040c0c07c0800403c040c2d01110155100c103002699214a4040c103450 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 952735341 1250 952734091 952734103
    0x10309021f024809040f030908030708091804020303041401020712030203130e060a06030b041103090a0302060f0c0409020318010c0507021903050304030b0705091c20010912050f070314 81
    0x210040426003418600c101007200781340300030f002400201919029104040c42039544000814509007241c1e1218414180410b103540140c607407600c20802805188035190001d007060384100c0e0001c000c3c42c1014a0700c001d41c01642600401e42d4114064580c1c0890341c0180080c4582240d0300907801140c41d07001480000e0124915604121045040d1300c042080c0340c1e40b035000740825555140b8002c100304a002000c2006410307036400c01e00101d58007004201c8079020006103401d000c1d0080e400c0710b2147c3c03102c821000c002a0103071500302d0030020402081c809052150015038021040c544060031054a844001d800c44600c1c90382c84002890000f600f600358501001c0000b54040d01c2d144403003010346190f8032290b4134412444010007618103400000d1045004100340c0e0103409015040000703518140220340320412841d5412100b210b41076251808007840941c00d091040c4ac10f8540080140c20072101140c1c201c1e03052030860300b40c0710704c90180c0c072107401c03c0c0602e10065201d6901e440f05d40c43c0400245003800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 952736591 1250 952735341 952735453
    0x17030412030e0c0103020d06091d100213050d030210060b18150d0b2101020405040e010209031f0906020f030601030c051c020d180b1005010309021f02 66
    0x40c10710502444002c00483c0100440a090800503950010755100001418603588a03da1841ca0701c190b00c990580c0d404107034002000c800703082c0ca02091402002404902a002411104441c800c5050015050041065500170300a00440d0544d840388620746080d00c10540080c00c00e15404585030000281c54402c440d20400200c9403181030f400b1901d203820a0380a45c102c171505040d26201080981c2c4c07101d04681d142e100d04480010360356280e42204902031342c800d200d611b0241e4a8900c3e680340920707041c801d440c45404010040d050304280b080d00c100c0411180c0c0c0000450507650700c00c80300003c0c001e20003000546291702c48240c6920b0b00d240050b088a010440f10800e018042189054030108034468000501c0e5031040144c48003000b03000344004254591740802000c0001d000c00042c00004803000d40f0540403040c4400f000c1344c45400440c2581c804c040c2c025049100009442d0380030034031028a41603021544110b400304442c160380204240350743c07600c000043d46140b03295011030302e800d030013107000b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 952737841 1250 952736591 952736597
    0x607150203092d0604170c0d050a0e04110a030506190303090f0801050103030503010b0f13062106050a03080f21010e151509030a230709091a0a0917030412 68
    0x10f08080256501d0740c400600060a01808002960107510b41c4000d96413107110240440b5442220314801402c640d00003402c40010a12101c000c42c06481d041c0201e000e50341600c1811410b0a0006806402034003024020307690294504281c1c8a240f0131121995005500036a070f40700c10307507103816001d40d07c2c87c2c0a45c000c010a64103200040c00840d400c03004590458920381e001d15a10b0050201280203409096039054401d002c070701000131501d03449510003003000140c01021420300c01a0f15a401110135500c0750542050b0780341030800c0800c101501811030203550444051605140c5240900000c0c001c103501741d0304400300001070144419140c5000d030b100704000364a103507007042c0340005103015140070241a002c8400182240c410344081c0101c030b03511035000c002d000d1104115010b0b4410040c803016100d1540c840c06d07500103048030a078080e85000076042588420f1040c0d88100091000d58003c1c100c9225a0311680d00000081710b440d040c0f46040030758110b86803281442e1804242d412054101e000030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 952739091 1250 952737841 952737913
    0x30e0301090b01120c0e0a0e06060409051c122c010b09150d0615080111031605090d0b011409090c0f09071b0f020a0e15060715020309 59
    0x6440d1500103815138130100d04e140242030051030030000710111900701c00501c4010b202405100141500604410b026141c196640c640d11781052108443d40420040c00f154804d00c043d5102c410051034803a25010380d45400a92001104c1d00301007520b4000d042440d4104046a0144440150062011080585200a00c5041d510794005170ba002c1001e02000c0341080b9070f4801c040907030b80748001009002e501c800e0520560074207015000c030600c9203101d1240d032075080c411121342d0114104201d07407188e46400032070344400042040407901a0007045081e9040301274050001c0114042d002c106000b013800400d031005440712542403141d40000540f803030590340c1c001002c007079190740d444081c001c241c2400d84031250a0742d83c4000481c1c106540c2c2d01c00d41100d100b04050700040c00149a03410103001c1c0280c51007420750745e443d0f80c0030503880000c4902d01410001d144c0064035510300f013401003044d18020312103441503400c09000340c0100da0007501d54050950080507100512440c0141c950101e00034243c43d008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 952740341 1250 952739091 952739093
    0x121a01030b041e0203010507030e06071419140708090415081b041b0503100605091324140f01050307020c060d06170303010608010b210a060b0f07030e030109 69
    0x18051000c2e100910510b804801044040c115807414031225800400900080c1450180603004011441c0303121510301a00300000c1d00c00d4040e43c140d03610009020006803070850f0b102c0b9241014003000c440030003000703144207100c0700e9a1400d40144c8000e50041004513501c0000760108000c03115004c10348180c42050b11000c1295000104003200720200c0a005c45490365a4140000c0091084580c04c1c2618101e800c02051020f601002440c42282d060340d001040f50b40300c00040e80d00d0f0080da19103960180c0680207065120f40c50b1f030040300d0178100c1315040208034000c042d0f94842144543d041045c8508841d0000e40e17a601e0700c48800118500282003403440c40c20400700c025162001c1350704c0c0034000c4c40d00050024400166901c134200030240300c6000594141e925000d86d450b54405c1c8680e0000a05050002c1602d5411030101c80c2c070820180310070554407811501144403000700800c0c040400b541caa03c0095881070a000406005004080c83c598500e101e14010340648000015140240c0c50111400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 952741591 1250 952740341 952740353
    0xf080a09060f020a110907120c02010c08180d11030f0d0207051009020f0d11060c011b02060c1204051e0715090e041704170105041e03121104030804121a0103 69
    0x3140001307003a13841b940c40d50f070307004400e40380c008401c003101c00503500d00801182c81a906500c0000341158982e00c542e500e0310b400f000d060402882c51b51014860300581494420070b40100020030207454030209407410058880062000d540290240200142e0001646000c01034280000c4241c2120040c040000e15076940104000d0b44d00044c035180903406196041c1e0901c0003101a20b112075000511a40c3e1f1910001503042c0070f00002c090320248000303c11300c002d54032800424845d204002d040c41613070810100301041c40440ca0301900a071402d004480c0c0c1c10b02c0051596820340000c00c800c1c0014030000d85403407e0a009241c5c888884803c1080c4494103000722524105210782007a000900f80c009071380b02c0c1d2520251449640d1101c07882c60f650003642c521801042d0002840b41c1c1c01204440105020050064800c0d83c0048004000483d113107040041c91099500280b01c0c1ca6420791081c0c02c0c140c072a83d07559860303800350300302901100300700019000708104032940328640328403501032507210b5265981301 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 952742841 1250 952741591 952741613
    0xa0506040b01060e1f20060405010207020a05091b07020f2e030204061d010207080a0f0203060604090206032e06050c06060105040614070618120e1210090f080a09060f020a 75
    0x340c810400d0000701070f9000d041d00c1c1d0000c0008a0100c050b07d1003800c0c2450014004e50040a080307010b041c034610001694503101034800e110b0b10b142d081032904c4040e804002c0b0030580c004082261301004c04888030340341e0349a540c0440003000418000d070030921000c06079001a144586180c02c20140104400d008a40c2d215003010f054100615680c01860302c40070040c0e0400301203800001051050305064020f101441c00c02140ea01c0c001d40a03038240380c80b030605000c140c45501d41c000c0d40180701040452051181a0029200d090910529100d015503880c441048001c00d41e0102c0c00040001c070f103170783c5854002c1c8442500304400b401e107185030510341807001e0b0000c0c0b800d8a020f8186030300466000d0a00c0455000421000c15007081e45015240303901d80040d14260031485100019286020300b4050308211900c03403080c0b44002c005042001c415102003020781060707803040305c0c1000d040c40c801000541d043c006c1d1850707005070f4031086406400c04400401d1111060884c8045512154414010411074500 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 952744091 1250 952742841 952742899
    0xb04031b09050f180d02070e0a020f161118010501050c0703171201230d150207081c0c140a0903140c090c0a0c0803070c0c03260f0409020a020a0506040b01060e 70
    0x1008c43d65685144d44240203004e075848110f800300300080c6019060213440c2102540380e210b08180d402841f4401d060144d070701b08001c2c005031522110030040c4000d600036006429450144000c89110545030356034080e49948402c0600d00080c00459483d01150841d4441400340ca08002030340d581e0001d40b604a1900f9000c114818025050769498100b80801c04014121250b490042595542c40074504040075078130a17207114550888119042142c02c2c610b01a07021040c4440c4d40f5010240704040308100319a1007842c0500c144140d2400020000300445101b000174844c11002d40049842c031030901008840080103490098070030885a084c4980108000d0b03039058010281e00d0700c82d52a000182c9000310011409448450318550001c10041e030101010b07407089040b00701c440303824451382c801022400380030080c04c6007046c2444140540803403030b4082c04108540e48111004c0030705075207409040c00f6043d0381c140d403d15010b5005210b1280c000400da54100e0055030346042c02c85075117200c10411211400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 952745341 1250 952744091 952744109
    0x403020108130c030b0414010e10020a020304180b0a060f02120d0b060c0a0512071a060411040f0326400911040b04031b09050f180d0207 60
    0x82800b0703a0240091891059100701054401500e1342407840803620100d07001c1340c6649016101d180f101c44103005804c0e2215660300249003110301c0354040c070065040700b498401148020300c0009400910b044010b180c0901240c03001170b15a480d4028002000c0c4250002e03400d00c0900a450500c06900080e448015407001d8030660312142440860301c040c10068444070380c032060100c1c40d2214000c001c95061fa200b0300c135208444441c594040800301c6c0d4050380c1e8000d8040b041010116014041d4400c00ca40e101038001c100190400401c0c40b5887c0c2c64005802c0f41944c0d41c10088180701b082081201a00d4100c6a00340c0740103a0130703030214480e01c45d12038100648458800c1001d65001e01e141c0c192402c0401500545181034241e02c8001c0180ca0480d0b4800c280f4000c2c1000da502c0d000303c0340501110240e4201003981403419045407200003804003944040c0716148818680041e090001d440798a0146011145280441c1452503d6114415140047e080b013070b04005000c1c2c10094000940300b048410400d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 952746591 1250 952745341 952745357
    0xc0503030909010b1e0a120f11070f15050c19140f070c05030d2d0c1202070803192006060409021207030501060602120f0a120207050a030305100e090304030201 70
    0x16aa240010245282e005d0f400c080201c0c1911503070760000c080400442414008001c40c010008811781940c15907205480e107410200500c1000c20150449084203034001c00d2a180d02110310340841045450449407852810008506101405045007640078603865500d440700103904000c02c03180325441070790030300c0145e0500003030f10404112007114403600412006056506400b443c50014120030f03103060411005000040104104002e81c820a009042c3e130b81e42c07084151001030740c0707040311390394860141400d610410b400090044010401010716800040851848988445011313012403000c41420b00710211101e00341c1c0000c20002041a840541102d002c01c0002c0b0794004180c001303d210382c0d1442180a1f0000c0403041c4081500540204c803a9a070888104014140304c407403180c0200c0c1c0303110b00c440b00204030b1940c856100e81401c0000401e02c64006181c0034039542c1c2e00d45010060402240400e403250100164124080092801070103c1c1c0350900181c60840300240c0c980c401e500000781072082031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 952747841 1250 952746591 952746607
    0x60102030f0705010f24090207080d0e15011511010902011d01051309050610050a0e013b010807020c0604030b100806011205100209031c180f030c0503030909010b 71
    0x35040094028442c1404000b100341c030800300156041c1b40b8185500050740d07200c0005001d0f0319072084400064201c00c5040c00c22483c0800d000180c032620000ca030381c520411020500300381416840340c0c020174511340220041c0524050181100e400400d5001c0282d15140c0742a0140c1d0300301d000c40720084000b00414064044103c0180c6880c000c1e003519460b110710f040c00100d4180380340d40c40240100004c680b03968822031001001c481c20b04c1104564030004143c143e0b0800ca41d402000740ea40c61882e80c41c00e6210345103203480ca18404841074030504d88039004000d20382c150f9507046021290020f0305840641090240704001c9112480743c0d120080400c0d11050015180d045400112405000c915055420304d580d01c03400c19800d010a04401d490030700503101a02810701c0c05208840303080d600500605248031020003500b80c41e0fa072980500b01840928949044050040e000d01409000b406a43c24800c90540c14150760a020a4014034000d510030130440000b580e40700d411504560094298070740d2042c2e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 952749091 1250 952747841 952747843
    0x307030c0c1716050f011b0c0e07030b09100f06050f04050307030f0b07081b0306030c0a08010c020c030102130b07030212070f03030e0a0b1605090d121205060102030f0705 75
    0x81c6500c408014110203020386a40040810105000d030030380307100198102d480c0d60420000c0701c048000ba5000c61100e041040e4207800a461344074032a406035600408599845110051501c001c81d40000000d0b5601386070441c1e850001101134009a00400c110061400d0903401e440c014424007803a0140200802c010005003034243c00c880c0a8240a000e44940c030341e80c2d1030041000032249000700c0308000c1d0100040e0310340b441140038901c80e0b2080248a0018a42c0d103071400242d40c4080d02c2c01c0e4150094014419181d01d0340f40400340203100d602c00000e42440005002820700054411262083c0d004101550f41c1d1030480c060b24003621410314620b503030795500349402c9e8505451404800780821000c1004000d202c030035282c944040740203480a2021100d00482d03e5101d4801480c000c1c1180850300210320300700107038a07900c48840400c1c18060f19103180400021000030000c0d20464000d900c001072105800d5200c50468000350444e5000d00150a081002039220b0151201526140d98080380c004113000c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 952750341 1250 952749091 952749113
    0x912170a1a0612011a0703020c0d0f2418020603070305061207090506010f03020c0a060209060408010609060617010f0312120c0305180c13050c0906040b120601110307030c 75
    0x41c00602041da1409641025401d0b12400d104800101c08103850020000614904031008660315501801c0913609078410800b1004a001c0140c8400e002c40c001c0a002a1178401000d02c1d90b41030150500400303201c240604140c56103007030803001c2094560841401a21000142ea8218440e41800304981d41c3e501e000c01d1268404c0d40d44d614517807061010018901d0455881035000d8502a40c8010000c01800e10980076031103849004451a44607102003004070f803040d805008150001440c2d2490940d440c0b110a081d2405600502546641e0b10010800c0c903802c45240041c03070007900400304640d03140c15151200d0070440e02c1301071b01d0f41b041c5d035007540ea0140c410085280c42c2c81d0582400c00214500c1e0400800400040354840e1081d0101e9903200c2102d40001152a0580303270050955910798449141e0f4009040003800300e4000700e500388408192a0ba4400207803002d040d810308603075104c1071403104a5090041c0603001d68180075000b607419450004c040100c85c4002e4040c105461004981c1c901360038400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 952751591 1250 952750341 952750391
    0x7030804140f1c03051b0d0506130e01020d050a0608210f220504110d02070f0204050403021b101d0307050306090706020106450603060912170a 63
    0x10045004124225880400f0400041469a01004103030f444284403d0031024409548901440910091006000c00c3d04005c3d406640580202c18440c04410840c082e42e102a100d401c90380d4010030102000a06445a0756200b100440244410b80c0b80070601900d444020741c40c80c506012481502d14080703910421201040c0d00c40a2030350750b404281829240703010140390700800c0c01c0b0003000001803d1400b4050f054543c2482d8500914150f00b9106140081d400f1000403190941120b007108050794551003a640710744d000e03030003900308402002c0a0414080358880d16602c105580b41100e810194000c0301c00100f100421600c1c00f6040a14001915001190303101c00d40c50711660b0100055135401090140c115206500203001080e00c0d041000901490541d100c80003440d00000c14881599500000b128032411410b035400d10450440c0030000d40300640c0080e50300d030340c0f292580410440c0d21001a07450000502d0451714001c10310a0401481ca0064004144141c42d1004021070070a500b8580b0a04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 952752841 1250 952751591 952751593
    0xa1b0804030e06390316140a030e09180325230f0705030a0f0218090102072906040e160e101509050607210216060507030804140f 57
    0x41d00c0252011029604c07036030202520b01109140b1184040101e404881542d040c000145044c40c050354000c2c161620a90001d9072450502012080c07503100c1400207020090003a5a011501000003007030004503100580302281031a0306440c07024040c580403040d0f40380c0c5072100c1c1041d04803c2000071100c011210302400905540e4030401c82c50410030101d01031030090705001c020741c2c6010b04d043c0c030581e4840003644109509038103d01101c00000f0751070f482c0e00c0300c83d9200412601e042003458040314007485007213130f0f0901541c1d4002603100502030090741c01000d404c0c4900b00c4500c0d800f001c00e80d54100150241c082400f13162607840d48040d984d03050146545003141c442d107880d840b0369034401c4144402e00540d40141d42903400138000c2100c01e5407504090116109464468612b4641402d000c00d40d4002d041c180c4810005090100c0848003100c0c1138110155140c4c000d000003900d422440302130003490392001041c0310040100d0f50010307800c119100e0340035400844200414845a61040c10810f49040380622 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 952754091 1250 952752841 952752847
    0x10c02040c1206060e09040f140a0b0403020c090103150e12160b090a0b070c02011b050a0201030e06060d03180815090d1403040f06140a060e0a1b0804030e06 69
    0x55408482c90b08040da18220600c0010303918102501c1d044d04081d912030304485a100043c0c041360b51a0380c07140340c50744140d00c694801c480f09035941e42003607403044086462142c403006200906070304100003186035804071501d04445d4510303030f1403c2050b180c911280c04526150448004002320501400d00b0350f0800185259860143c0d03d00801400315803003044a200032501e0100e1291840054008105075000b103084850b5214864103491518002800f241080038081c1c060401743c4015005c00c264901c19401460100c90034800982550f86a14000c20b040e44404208610790751061003140303200e501810400006030001a050800c038101d504521020f124650a01c0904450411524440d20b0340a09485420f40103102c100c0d0240f518038a40c0e420407005001280c00700740e60300111000d82d032151200107040c04144401c0312040c80c00310703440c4003c69500e4004000c004020341d180c950090a0000420520700c1100044c450074940007030440821140a00107002c041c0211000c03503281c0f10051641e51 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 952755341 1250 952754091 952754111
    0x2040b0a0311160b100503010f1b08090706110715020618070e0109020912120c1e03030a090c08061f0905060a0311030304090f24030b070e010c0204 65
    0x112039488451400006032910408440c2500315006407105204800c1101c041d90080340c0b0707009900c020141c030070400100000400200b66500748290592200f00900100d54184005600305c140b07075600d1074600c144030082c0c082141d0880c0200d151420f8a5090070200c454921002d019403901d8802d03084504020a039560094a043d00001c0d400e120743c054202d200d200d03100901401d40c0f5140b19124004102d04e40348018080c2d03401680251911000240c206031403a080a80142d02d49001c501c000d040c1050009040c0d15803180c00c0c00100a10f4980490410070b400c5c04803042552444010000c0000658600f2407100308202d4045280007001088122951350404003440200171400c0b000b1014640080200058201454003416100d004000d1111410f140f03191550381c0302c4da02110400d54903000402c004104113185109507850480707501000901c40030f40e12000d4126442d02010b140032014416030070400074440c501d51661080152820004581038140103031801080301c00000d600500b0400310b04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 952756591 1250 952755341 952755359
    0x2130207020d440d090501020d0902120c06030c0c07051002101b0f2706050405030705011e030911060d0507030b0109050f0f150408070e0a050708040605100305010204 73
    0x10300c10790004041c00749000d8046030401a40d5043d0341d03031850304143c40890383c4022895000039241e0b071100c119001c54071402d165160381c00c81c0d20003001401e699546820340c6003035044c00c1e1481070105030b8000007450900040710001d60a40002800ba0043c60b40004d5117003040b800030700008008080244c5080152103100310040d488080b062000d0b00b9103803030b0583c01400d1200309800084c28814940380d0380400d1804800c11248140c95445880003102142e00c802050111aa072180c02031140d5075442d9200c3d42458101410f0110b0b07648040d04002d080c13645000c1d0316440034840c1c15460414240024554010b00d001c020000c90201c43c558850408617050441002c50303000030780300e491f04d40c2d000c001710303086030b8010344000302c9a00451b03400240140141c1c4145c20310a0b1116642a0000c24040e0000c105510301003060303015802004081c0c000c40020030195400c041c84a0b000814414188058035080a0041228030000c0001c1c0c0002e44590208940c164059a40400b40d40c0040081d5030340d80e182c00801c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 952757841 1250 952756591 952756613
    0x51c0b030a0503041e051c06090c08010e0c121f0e0105040f020118061e02030903061f080105011809080904050c180d02030d0e191806060503040b0402130207020d 71
    0x170054000d100003112451540600100590390001d2504644000c901d00c0d52070f00750b840c2e1104459895440109a010030308598000c00100307000000070603030503400035119080815000d03446005080c109800416002c02041440c0c0c0d168800880b0b24900141c40a900090b08001039030302159440c1c04140800c0c0324002030380c3c00066000303032207012821400829560700b01c205413142038002000901d002c1c2c0c43c10020540d403440001984100c2c3e044c0202e1200003410620241d80707104649413480c01c2e0400e170498201c8480001c000d00c0008201c65072601008806020f0f41c500801c06440d80c590002c030409c82007100780c40c1e141001400400ca540b034024040d45040e846910b0040d00380540200d011403a2601900b103000030340d4060b002c0c2100c200459000d0b20f03420001086d99611500340703c5c0203944940c20708102001020ba4403080c0c4800c0c40c850b44024211010703900301030108441041008042004121450b402941c142c801a01800e07250340c100009014168000b54000c4188000d24240042400301c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 952759091 1250 952757841 952757849
    0x211110170a02211303030b01051b0303040b100f12031b110301050903070f0b040c0b03040302060a0c0e0d030e04020d0e030c06011e060e060d2d020a051c0b030a050304 73
    0x9010b0f2044440403d01051000c03c42d00002200445003403030000034400c2c0c0140d001e00c28107040803402c12a2030500c8541104c0c1d022420100c40d44080100814004102449a003110b94055081c1a0508009410000008034041c03112901d507045010b004240c40364002400c54080e2101e01c00c40b4042d2460203100503d62051018442d42c03d110200da19003c020040f41c000c00e41c0602c010910394080d58030050340341e10041054520800d1883d0000720014020011481030b4400c3d4094202c5203003102807001112039007154002044000c41c07808001b9181c40404c0b1020f15010f0516004a0b149400090080d204101c4800d401c5e9051607203041c03060038000060000e805802d02552503982e00c481500c1e8010a0024101c10704880070301e410491203018243d0310403003450181042d45010f50b40340c0c580e010360310502c608030f10040e071551540c0801e006100c0036034418010100294900800709100900b1800380e0b01c0034152110074050201d1401c4056032007141c01e454041c00fa02c0b12000c1c24180162241c2007841 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 952760341 1250 952759091 952759117
    0x309050111090a03030c0206070605070c0b010f050a0603020c16090204060311120c03090721050606010e090711031e04030c091104031202010b0d0c211110170a02 71
    0x71004103004115002d03900c640030b01414030034040b032442c1c508171012501406d0681e0016002c002d07110114030203000b15449029540c030b8005503030302c5a04d05110360000c16408072024440da0081405907549841c9100c085a08526015032120405d8106905203940d0800081d5040881340000400030b005402500464407103072410801444100c107005054458000201d0103960400c00050014030340b4030141d5000101503045580c499201e0343c002c264030342d00c0103000c800d03160500703e02d00400404209290340107100b0b1038100450840b140102d2003003031015101c107003400f01004d25046c01c41d03c10425500c44580385042d11a560074070700c124000a5120703010590b036407005104045400b00d0716005000d02c50080403400c91602c0c0c650740b20500400c584903007a000b15501e400d004076083d82c50842a0b0110390044d800c100c031644c604503421040c550b56100b140c034040f91003504240814650f8003010f001220640310100c40400310103085a04203459500030441c01200020321100d11420740c0a0311030001010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 952761591 1250 952760341 952760351
    0xf050114100504360327090507031a01080a0905060a020a3b0a0e27010b0117090a080408210403050309010e0112020c1f020307230f0a03090501 63
    0x50b0b40d0494801c261071444c90401d1100c00071030580c0c04052024135440e4028030705200c02c50440c203002440310840800c14411460f03e203d0512440c0304a2140365000300180c1400c01040a440350110340d6404400b0080d81400103030703000030380d0900032504003a410380d91150907a1078505d0900c010100941008ac00b00c400a60035a0420405140c49440704646031048015096540030713901c1c0a90240d85a640216000321945400049070a400e001b12406990605500302c880d110602624030f026a408039041020ba0416805400380c0e60030141001c450704281c0103120140e5542c51616250440104004060000005001900c0003011031001c0c1c842c0b041503000d5140c1d610045045910340614040640150801c01031a0703001d40c041c038168001c150041c1010547d0300103003101d036422030f0003411000140b6008080325030b1103070b95070429170f036070003403450000f181541002e280040040c22084441c103c00c010011751041c01c174103441c1c1660390070001d00900c0c0d40c1d60002c00c0340080140114960840d0103600344 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 952762841 1250 952761591 952761611
    0x190605060f0d1202010219050a03050c0f04090906020702030d110105010f030c06030c0903061d010518060c0c0118110f01210c090f0b03070810030804030f050114100504 74
    0x20a20076454100024400c03824120582c48614600e840146210306565082140c0c1252010424030b5946030340341d54680d00d40301c512020001c0e0594000424015680b0400c0010603003c544c020203980a80d81000c02c009030481962400c04024441d8071400395052081e045800304642c5c0c0305004d40c042c603412200134000b5990740d10700c60040041e1400020a904800302040c031a0501c254070055985c7d00c0c9103000001c840e62034952000f103a00d509613000e45500b0040c400c01199109028094000d410120b0f05c840d003421030500c054071050040e0042680000c0041c00e100c0440e02500f1160070203400401202803000185007040045070380e481900e004440c1c400c0c1c104440c0d070150f000740b403512402142174002c812842c6014802080d01c540080c1c140401414003244103554800c510010309a002110355590901c0b0901a00c0f42500030898510219090000d000203529402941c2c112540291403101c010000d01e0030f503014081c0240b94010051046040110030301404170310104484058400300400c4c450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 952764091 1250 952762841 952762849
    0x51807050915010315180b0f0a03060504050a0b0a020414011803030f0c0b0408040503060108030408100b040902030a0b07030507050702010c15061a13060305071d0303090319060506 79
    0xa4490540d00812a00028103100055011420654014900081d500740e4081034484041285d0300403450400c40b1400c90381000200b885a0341c900201294503c40c088040c070300141401e40386020040c800c0742c40d2400b2030208034042100070740391035000c10203215615100c100440250007520544404141d41a80c45001d9400380030718940c610307901304641d003480b802d5071015290308902c50710040030007a00c550f4000118001075190790180784295100b0781e0341c602d17082c00c152070160185c11401854004202c02c205c1e82400180c070807010500444c011450031103c400080042042447c00394260145810b01c0d0204030034140000e1145407661410082511003940440e25400751442c003e01185011a0300320205c4c0c030944001440000f50b4601040090703c45520440400c81d801480c80200d001280100c004846400c074140607220714a01008030f4503004000a0000361410408100d004081001c511991001d100f10f804000003c1c1c2141d00e01c0f04401402600c1c0004c2c01010f44620740340c040030460030300d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 952765341 1250 952764091 952764103
    0x100305010e0610020f030705010e07060908210f0d2910051e0415080901092109050a06020a0c1e0e090102040305190203010f05090316030507150518 65
    0x41204051011030ba290307400e03c1070006403500c0b0b00043d071141103032075803c3e240100010842144a00004210314803198100e62811445070031032400d1054540f428881d0020001d0401440e002c0c46803a24421302c0d8018458000d4400d1122500c100800007c070100d111340c46421101c10305400600103489200c0c040c95841000e030040d140d5641c48007030b41501c404414032820140011180c10b201c000a0003a1482100f1902d07445544400000f024480c0c1880c41c071071300115040d6201d40010024888641380d4ad55a04600c0e000060000718030f07100d8008a0000e9201d900303443c01500c1c01502944050b071301c0791030103540d41100c01c90032212981054404a501144150100b0403602e01810a00c210303410615141c06080000b0410800d5650a010000100f0340401030710b0500d541c08003500381e200c50140141801e42c0c410850701502141000e00744240303080b00004440780d00e144a49141c406004500d0304482600c18000301410b059680e04070070948807519442180640c0101d101e90300c50b0102046080c0d2581 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 952766591 1250 952765341 952765349
    0x1f1e080c091605071104020408011b05030601080708040f02120303060316150e122409060f0414030d1a1002070803030403080604060b0a0e0102010b1804060e15041110030501 76
    0x45040c0e41000b424021009000c0407803040981017110030b80d840202d801c076041640008017582d181d1030318040780002030a8000e9003121a14000c0c0c070b1440c2120019085490103000c550400c900c074000030b014044104540e0b8651640107241e22003008102c1c0c04550b4a400c1036980912030b000d080030b1040f00201c00e6185204443c118411200300c01c40401d42900c00c94030354519641c000745041c1c0e45141600042c0700c07045800c0c0042000d020000791114071001c507c00d0041c07114140d51b1008060103002010303041c03030b1944250300101f03023200b0032815400e07642540520485010303120300704500e130195102803008070042580291004c4a0180720200f0490b0340e528903120301c9030180c100700040342c0032070310490b1815800040a0400315210f56500041c2c10340340c1c02a061480050100c80103008a50b07828040c00a1400c400c42c4d100900350540708174584203090261005050a60f60356140e01e549809000801a40f8440c100c409968603050070000d0404402c41c1200c0d220b480d01040c008a031500903c42c1f14180c0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 952767841 1250 952766591 952766611
    0xa0509040602030901090f1b0b03190c1806110610031a070201110c06060f0f0f040203060f0a062601060c08090d05031b0105150105031f1e080c09 64
    0x99252925110002c0d40b020300201d02c15501c900c0c40d5804030f0060001c000d9054801c0441d42e14a400c108110b010b0303030170260001c2e05a803c00b0002d000c0038243c0031656003400c0d80380001c0064036010f1080140c0e00c3c00092004418005151074000480300e07008280c010340b40c001482074890503512400e420743c0c0c4118500000784111805518001078940c4256104c0d4401c520340000100788002615100403078025150400d89903014400b001924140007104a07035049003922003050056078500028455524100e4090040340e0110000d0400c0c0d981c001200007500c0080c007600401511410002d1141143c810814211102003680c3d01c1d4480c14044041c0c12102551380e407001741d250550b0b9003001a404543e40550043c0c0017080207010501c10b01c001c00345d004004c040030b82024990f400180c00d40e44001d019003688008501a507a460343c00404490b071066051802c242d41070030712021030180003226044500a1701c80c0d40a20151400f145007032000341c400040172905902c0d0030310300300143c0034400c403260150 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 952769091 1250 952767841 952767859
    0x22260c042f130f080d0207051c03050f0409061505031515070b010e0109060f031208250c030809010b012c0301112101300605040309080c0a05 62
    0x80051032600300c1d20880401c145894070505071030700101c2850750b80101a190781095010400b42c01c04000032508040306001901d901464030000549001c1c44c2c0d1210800912841c2d0b418081500c91021103200c510b50034140d030340301d42e160002c4200510050051400084003010a400d20038090001d0ba4401d02945c440144002141000d0144041d076895610400300c8003804510f0028522550740b6018000402c2804099894031940b041911401d510004a1019980050021031200d20700741c0705000320303802d2000583d121040390404007007245002070088144100e140ca50f0340e90010818a802d07010390340b0700c103007611001c0c2d4103422124803030152030204ad0400e010708082c0c4100c001d010303007010304115103e125442d140007080c00c0d1036249640c3c80004100080d000543c5043ca00d4101100102c000785403c0c540c141401c0540d5100601807441888020381102200191002c1048407030700e078400320605c00c605007464007038010800c2d4011041c00c0d004203c6e20414a0405015403002c80d41e0003020070300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 952770341 1250 952769091 952769141
    0xc03090604230613031215050d0212060c070b0c0412030e04020c121c0506010c17040f060512010801050c1204020f100914030c0622260c04 61
    0x1c0020540d8900c140d8030044400a20b0074410500c040d0f442004410f06410352111540340003010310220352101c0d02c850385098600b00710140c0e8030460398107541307056a15807020a400e00000708042610748200e502c41c4643c1d02004807040740d03080507041541c070a03620684c40e0b807030f02c00364410710b405030340560b090301d200d00d29240010030f1065070030910b0000c002e400140b4182000c001c141c10500d083c0a08800800001603000144450f1481d071805e00302d01d0401082a0308000d40000d042c1b084e0040090102d5100030031580c0a0ba604d2400c4030018890044800920f59032450090000c3d00042c00400703a40b15020000241a130040c09241e200310300b80d61905141c4421804040c0285401800c10b81e0040032407910f10110307440c1c502e104803034070401e52590721009181030401062002c5807200305d23001c0d81101203100615182c00054030140541600040d404160001200e805002c00342c9c40b030300501d5030710800826016051948000c624207000b060b510300f580c040050100303480c1c0c81c0f28050b42039007041e00c03492 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 952771591 1250 952770341 952770353
    0x103020a1b0c080105010f060e0a06170a2d1a030d030e0c0a090e07080c011b0302030d1505010e04060f090915050c040905010e19020d0b120f01050c03090604 69
    0x340160b10528110a00b00e0315200c400b821540c00b40c11a0002d100c408809100d165004214904510000c4a00120050820800034801480c82e444481c201d60084040b804040e919086611180c0000c00344195000b0703258811505044c415040c41000390ad401d144a10030035602c80107d4041c0c0d406001060250701808040340207000440d880d440c60b00072b0846c0c221441d5200800140184810100402c00c04800b0513882e040100687c4400e18545c0101d0300072100c2d03600111704802c0032105101d1003a0202c89820242c4c2180704011040050910303042c0d40107410102d0240180c1a90402c0e660115004148800c5c04101c0b403490107000c07940c5001c404204440e0f11280c001c01c0806104e110311039074060020741b0315003d43d00141c03500c0d00020004039003800081c0080c40340380d0040c1611451030b841130801d10f807000408221004400100b50300000c0500f0b4002c180c3e007110700c4c0c100001d81440a00c010544003179450700764916113000d4550910300421f028402c01400d407406841440e02420940d26070f941d0354 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 952772841 1250 952771591 952771637
    0x70e04141906030c120b010b0c0a150204083a12020c010b061201140603010e13031103120a110c1c09090513050705011d041d0105240103020a 62
    0x5041d41d49400c000b000007482c00f00da4400610400310305411814043c51300c482903001c140c10140d00343c1b10501c500b035003a090011b09002140d400401400c49a22100d030290003034403a90b00a440303030340700c2c0305c1500340c600800200740b5aa102232014014422101516514031420b210540e210000b4024540c031100c2d070b406d0782e00400000300b0303240001075080280000701d05141c0198010309003140c3c682004008100d05290030040151080310401d142d5810008c6c2e0040b551405007022105140d0071000e0820103004080340c00c2c940041008407a00c640f811070751801f610744115006500141401000e4142d803184200340c40c0c0508e4018058681e410111680340c0303841c030901000404001c4000300c002a00d05403441118010540003605607070381006c6040052400203194443d5040050349109000d111040c150700003070702d190807100400c609414420f4900014504c0030820703c2c9501c4c140c1802460780c01160000d00101c02601030704015050030006608a006400d01000031501c0d031585000002004017103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 952774091 1250 952772841 952772881
    0xb030112123615110d0206040308010b07020a030506130311070f051905040c0504080606010804020a090905010b1c1e02130216050a030801050109050910050103020f070501050f070e0414 81
    0xe24a50302d5492500312210000ba00c10742004c500b180c844151074080600c80c150841e0442c0c00241018105960014a00d80381441810407240300400c5440855031a0103000c0c0065400c8030480310340f402d001006007807550300702008501044101640c4845001c0c045a580d04413480700300310303102c40c510304000d1001d84035100e119560100c10b4642d02044664892050000181103582d409840d83e08041442e13203482c1c400340c60703a0f050096071002c0000503955112010140c1da091580880d0781482e0f0320340b550141440c840c0c074aa10840c0d12a1541c0001e107142903540c0c0c00c80c018209000c1e42a0b085c130b017000750403c0d8800701940040c4501c029429003002d030b0b002410020f0340e2010300000740c4401d40380c290400151160480004450500401c0782d50390002c0c1c08405010200d80e40e4400b420804030594880c40b075031143c90b050607004644c2400e0303000d0180a80305d2640c1c00030004c2c00075150280c03000007010b40444040300071402000d40490941880c1c45010880c4941158001c1281c403210070002c003600344989 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 952775341 1250 952774091 952774187
    0x15070f0305070f0b010f0602010203091f11030f0402030d0c1218050603090604030305011421010b130e060a0e030306040b2215080309030604080307090b03011212 71
    0x2c01e080005828030841403259024510030040d0b5410082d00c1e2840390b0b002e0f800801160b0050042c801d00350030208035114030079085040d1400703040c1c3c15420213000c0d01c5140d0307060318069404401c00ca03035a42d004111034030452088040d00ca003030303203101c4058500d0315088101500c4010315503d500c03a514080c0c2d00250044c4001d1260f00200395460340000d460340d0040703951400e150000380c240810160580245805000e428449501c000d03550000300d8403500311b107034290b40074050802031400169029071001d2480e40c0090300494920388660068070141020442035082c0340300347c500040000c600381c8a202c0040f03101c0e4028510b107031039040c20000604401a045a444607000b03284480044d0541e0000515510512000c0b607040c2d844010350820380d020368440b80c0c03d41c10400000032640d9000c10100c2c0d01c035030700c4102d0744c0d01c0c2c0d2180310007102c3c18006600401c083c0040003002007000d1000e01048240c2e51701c40c0ca13884680d8030056400305c41114000740100c0640e132603540500c0c0d101100c00c00c0c521003041400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 952776591 1250 952775341 952775347
    0x21020909030c060f0c09010825020d2c22020c0115050f060a0f18090e010f0608030301090f0e03122505031503012a0e15070f0305 57
    0x50006018400203803016440341c0d000268404802c9014802c1c150304c83c00300d603524501803420400101e0305204202c0c080e81000441c2001800e10886044040c1030042060050410200e81c40d8000e50344182041d51040851031800040c1c18a06865000728510b5080d004010960031100d020b010041c1c04801d000c000040840e8060b10803140903102510b0001c045100100d12005250340700e4000b040e42d50001030251807440703903100c901c4d1905c0c022203d0555040c5484420000513140440f00c3d08401c0c0707541541c0586034040000c035039a031508503801004003100208940f4441000b40f0080701e201e2702c946607880c1c20501c0104413160440d070046500002c2401c01044820166440c2da0940d880941c03c15a035070050360070700400001aa50381c3e4908200600da001242c8041400070b4142e000062207a100d041c00e040a164090b1029003140c05001240000421001200d99494205002003c1d04070000b404e040340d8024149045041d01021001024010745000200d8403083c045000c45042541400420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 952777841 1250 952776591 952776593
    0x90f0d0222021305010201060b0a0810030b01120c060e010c1101050d050f010e1b040905180f0c040e0a0b01050607020103090c0605030123010e010804020102120406020a17070c21 78
    0x1000108500440c0d01c8001039843d400f5042034a094078458006604681c900f400a1000501500856602c441340e410f01c01303401e40e503030346442c0020440781d00005c1218104400008817000e6039895020410320481c2e0100070305440345c00803107610356492500c40c009605e8040c0307040880c010964901c10382006150561130240c144da00301007507420030b541310314004044000400880c4520398039a0b40088030000c2401c1c00000c80071544409000c1d41c06021a85540d0f02c01190106144401c058030a00c044c1c410358400003182c01801d6114118003c0e15401135041c180c0034164203002244001c44203a11585030100d80c4d0030113040c0461a0000c1000300c1c10315030b4030130b0400041108482810014070590f507401d0303070707940c100b03050000b14101141a20411041c109080f090710703a00008507000c00002071924404c0d40e034460004030f260264504c03242850741000100414540d6000c039803c80c005020341007929000610058490b88c9100c0d460001d000c510203c034041c020800b40014a271081d40801028600c80002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 952779091 1250 952777841 952777879
    0x30304060c0b090303010b040e0c0912030702010e060307020d031d03120403030b0f0d0224160c380909010b0d150308041a07060908031b090f0d02 64
    0x140c00610106035000c0c50078080012030710160b684101c40001640c1154075118100d60a8005d9014103194101118009035000200c0000e17a000e00000400c071155071b44603c132500d5125401160180d00258070342e8003014043c20303e04202c03805001540e00500c540100000118020894009650352001040300d20700303020181003006d444c10302c410081145e03c0c0d061925000e412251208422402a0700c5036004040c1583c503020800c002580546000304842c0741342d0074410041e0041c0304055000240031500b09100c81031040b540d040e0510403015021201c0e26449400c1c001030307a2541c400c64028480d4003a174079444080341e104001050390003089040400d41000590b052074240c00c91403d00c000429489954040c90241d0b1080104802543e10b0b550300359100c2c00198400c0d80509408642c4000300d042c5403030903041c11201c2080e001102001031541514244003a40d00580e0709056a007800300050809280e5041122901c040081480c4084a0748100b4041040c5500100384d900024a61141e100310807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 952780341 1250 952779091 952779097
    0xd0509041d07091b03050106201501170c010503100909020a0906061809020a0804030509121002030f070f0903150207080a0801030210090302010503040f020d120519080f240303 77
    0x2c05804a940130401c00c60031241d9500c5901c1c0c40816090400411160350400fa40b0510001d8a2450b00d6144c61342402c6246403500340142d186010b50640c000294400010340d107907090130071580540da80507060000440c1c55000503615000401c500c0d0740100040302d0154071010110703101030040c826459a9176100b408640c4180d0006002c02e01000c0522a4180305102c2503010705900d480850508480707150042070640c00501c01401d1000c00100c8c000c1e141c2da50111800008410030807500503d0555402e08c0c0030b508155803280020385040d000c510b405010300100101c000141e9121900c039495600c40444254000b10b00354040740d0300300400340c04030362008001d098a660944403001103502d140f0510a0b40204068400d0801a13084414070061382d0080842e40c2054104080885d00201800028514030322210020a8001489000300d10b968101d00a440601c000f400741030065428040142c03404841100e11034600450325000907910045450345045900040d001484440843c5005c43d265078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 952781591 1250 952780341 952780349
    0x81605012705031b101b170f130524030403051e04091409160b03090304050a0620190b070225030506010b0a2109020d230d0509041d07 59
    0x4d84401200203080010901100c00c0891400f402c040c1580b0041c403400301d0058000070083c032140b00d4610f4198a200c401e0300d00f8980e000e4941036840c0c411040381c1102c80158441c81d402034107244030704c080f101091900d00000340d0702e40c80142d20f16999a9002c0f120f6911002c10824610754483d0060302e04074684c40070300042c1c0b0040c240003503423160061005040040c000c0c0943c20903404030f2160522500710b81004400c4900141c2c031282c981d16494000c5045006507000355030400f5015400246055100e0881101c03a004103460752507094070303001d1003a10340706801c010414111000100c00001042000e940e60f1004d0315205403a91016100e2080c1c0c130130b904861096900e001e140b9010300c1400024412030b070041c600009020f1030402041009014400018450706803103c1c06c4440328203060541c2c00c0444071640c010080084a00c0c1c40c54050f40d80c0d00146034180041e5481e1440b51035000d0001561000c40c0042e45460741032002000c20400135006d4404461502510038441030114441040544068 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 952782841 1250 952781591 952781623
    0x309030803100b13061e1b0201090e340504030803040206070b0f0105040e070e06060a020a06020c030a030b030d3504051c020604111e12010608160501270503 69
    0x1032030020014181a1100404401b00c510282030705c000d030b6000b02c80200904044622410b06412034001a5404140b81d4480003208070480c0c1000106120180102020100c0c56000c2410300801103912400c10200d1100300c0103c2d50403c000e1003c5280070000e560f07c03905c024001450800c0c01e03581c0d910031000c1601c940713501a03030000040c08285064080c0c26200c00414008222461a0250321000d078140902103034044c80c000168103051a200303010324404a6000a0107559907440250030f140e49510a0403041c002074500400451680307002300c1c4c5c4c0c12030100503a44580751b041104a000c0748140c00304462805c0041407a070a0140510b40c108806d01c82c2e40100040d001f42000030445a21007a18080b600007103400103010840002c9030b50503010b4036683e043e60f5070400711840c00b84844680302e402c10f00d50380c0401c890708040b044000c1501700106503022101924000000041607681070f40342400b507607000c10384002105600000b210550110755903000d0034a900640c0d1000440e0604c264040080c02d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 952784091 1250 952782841 952782877
    0xf0c0f0d0f18021c0318030b04050c1203030f091e0a0b0a02130e0604230402190834030b010f050d030c0809010e15040f0905040309030803100b 63
    0x10040c991140e03526003600c03502400400310b640d500081030059400509102040074005001c01e240c800c01d4203c007040da0303015542c2c00054882c1440000e502c01160103c031039218514040e0b400d4280302d61510203400d04400114215207505001c491b00c1c0c42c3c002c0c903495141c0301e104c446010980711030803410045802e903c00342602850508241c3c201c1d220050282c010180100318040e41c8984540041003103541d400f42501203512070100007006020300040140032a80503402c04110100101c4015020314400c4132140191072045004c070404581c240b082e0f105580214a00060180f4091041404841c2c0404040106806807a4500d0482c40700d070000d0740c40741c92490061060314002e00b40140035150440d00c2e100d511416640081038000b401000421001001c1011103042c0d0240c208213440060042042d6600c50103c4d50500d001d412910408100703140c4c000000804040c135110340c1d030140d83c06035075001000e403e54403800c54580c0081c1440204003c006400140342a0000207000f4040c02005400c2d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 952785341 1250 952784091 952784111
    0xc0212040914150d02010c0606030f0303020d0507020a0209061903060e03130e09030304080906091e011b1101110f070f03020411030618070e0402120403031407080f0c0f0d 75
    0x4445000104038981c6228240307542c0c00c841e070f160209040e0035642460951540b901f075207003250182c0110f03400140b010303805400c10000c05815401400100c0c011040400244e80c4502c422a9900c4182a010b5004000d400114103281400e010046c008003c02d0740c00c40130681e6036540d4400f00c0300d02c41c030341c0a050303040826a00004540c03001c0c400010103c0d00004840c60422a0f05641c0701e1201600c024100400011251600d0f15003200307581485030020240d41c8424000003107540640c1d0050906030000d500c145c100e5018404182d010100749421103481c8080d2881800150341001c001400301d40d1910464030591911107013001000040e140e0040602001c2e4a0346c8140025200c4180082a000b02c0038010092543c44130070f103180d1a102c80000c070000d0307034513080740a803401041541c541c1d400c03500015040d8000b6400091f05405180b10303640400401170180020a0320030005d41d804000100000d000c5000031a032080e400c0d070000040d410a51408468044004455212280900017582c640080d81 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 952786591 1250 952785341 952785371
    0x25171b0312100b0f18010c05010203070315120305090f030703050714090a14132d150b360720060108101a06040f0f14060d0c02120409 59
    0x1000601049150a0901800300c0701d603140b40c044c1a0303403a015960380320014880c1b41e12800301c1c05039494202008550341d080001c1c00401415400f8100380254050410004140030804d11025481d03030940d036000d080602c12400c200780c141040d8266585407080c8840440450310520081004020780c8641e40e01d414040020b024a01c00d00030712101203140f90500802c0760003101e41899030300c1540c0318506031000d81030303161419568801d007881503008410b0007581e000c408580510781c2c20741405401840c01c043c240ca000300c0d0a4500c07425204c1e4100f120042d4245001c401d1086e0740d240c2d1010800d401c9c04031204003849043c03040040350000005184070102401c8282140031840e0314194042c0070300210343c1455102907903407012030402d101a5946103000d0254001e10700c043d030034046c001410942d03600e035150390402021603503020f206060b442d41000082d0440900720140600b80010b850a1b0030319110406044c0148100d01c0c100056014800108401252010042002d85408040020400e0070383c5440 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 952787841 1250 952786591 952786621
    0x9030315030304120b04020d080a02010209010201140403050901050c4e030622090614070503010e151c0303051f05090a020322060225171b0312 63
    0xc40e00a810801007444103134002040d01c0c00c07241c0c010107949082d440380c0c4049441c0c1406d0400181140d0030202d040305903d07906400601c0c8140302607000b44188080b0400700f10321004151001000b064040140c80f103d07501420150800c00707512010b0352444100315400f8501b003800703941e24075101c0400e408420101d45078000b4102c00142e001c1c1240680301c510030304a5500e884041e2889200b800d100d9056820302c004e0407808041c030010031005100e443c4403450300e80082c0804441c10f586074990040002e1005106900b640d049030080702d42103180e038031281442e4030391617160b04005410541c6107044003a010301198520f001030b40310303990001d294585402002540415030214100203802c000b02040310b980c403040100d40044000d20016540c0d00c580d02545482d151016601d2a22030183e6584024030480d9409009110305070124000301c95411001c00caa0540b508800400345162b4170f581070b060b080300101071f02c51400100215800d1140398040355107150815154900d0968040c0c040000352b154141d0300c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 952789091 1250 952787841 952787881
    0x71701021b010509060105040209130e06070314131709060a0908010e070803030f071116090b2205071404031112010b090a0c0c0c030b0a050c09010e150909090303 71
    0xb0043c50421228080d04e0f0b0f181889040c0c130890300030074001c82aa841e41202008100c3e048000c12803100349545140d214001240c412010070f02c1c29621110303c498070110141701e159a40e42c03000b0984500d5a0b80410a40040825944194288100311090715060001c01e6000c0554486c40466482c0000e21400d4810044803010950805242040810380c00000e0b250001000f0f98800c0e4959150328084501c4145e6410050300c40c40340b00f0030118a580c0d480340600503110850403d21404441d1820702c04c07030b10b01500210b034a5181c011480c1c1e101c135689910441c1c1111881c42d00e048104110407610055400580040d25100b5008101000d545809800c080c100301c9404024444655030500040840340b0003802030500e6503d51007844090351044200344183e40d481400000b00315100e0038445460442201c0c40c1d0206454600400c0d08500c203c002d6501c1c2d074005a40d040e5081b0114018007445421a860480c0c03110410f1101d840302eaa20362510741c1c4180028402107440c1c0c40c003540384855807040c00070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 952790341 1250 952789091 952789093
    0xb04080105100f1409060301201801090b0f220b0c0f06101203020a05010203040f03080708360a050319050702100809030c0f0607090603022a071701021b 67
    0x70341040240480d080f14180c40300112880d1505d9a9000082405003611145a42001c42c00059a0500034a0700c4040e00b20103e241104010380300c00f190055070704808a00640c54407800034002c1c1c0f803925005030010403202e8007003c141151002041403541c451203982e0000c08034400c01245495803440201302003140e80090000520090034a80400d6148810350b0059207017480403c400d0b402854000c00c150024258050001c556a1500c1c2c00c0010326194480c1c1c0c00c40010340100080360142e0321540d441c90040384460500f01d0b90b40b0109030003609039200e0801245c00c0e08908041200c140300c00f03000c0132204d07500503406180c0c0c541302100c1080214085001d900f00707000301480998003603255144902e002029905181c001c3c0c1e1910060b8501c4c50080c5041c50507540f04412401c0c18020001c945907005a49988407440140e07140c000907010703400750f43c40340303101c01d819243d07014003118291401d200100303c404280c5c0c086a49400d0278006011550040c0207103613400081005c4c00c2c2481519035009114858 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 952791591 1250 952790341 952790369
    0xe0604031101140c0a0c03140315150c120903010e12030702010612030e042d0b04060504022701050c0f010e061608041b0b07051f092103060b0408010510 67
    0x813001d0a020381e603259004c1100e50380025003094066000c5005070744400e02071645070f1920629a0040074000030986000c1c00b51030f9a0201072070700341c000345d0301902c00c090080e1001407a024040d20703168014000c495415901d40d00c609a00400c18002c020f600c0b0f000c804107a540c0e1901c000041c0c291101c55100640e80c18505015101280d80003410442c0d0703140850f404100f840550300031802e0301c0b085e1107441d94440084a0032100d40c1c121540540c6c04410180c4040c0185079480d400c0008a0241d070481e0041500303803000326a900c83c0d018010302d220000506110b03050181241c1090b261043c00c82d07003107082c1e030f544183c1c070020480c1c100091617000311840429000e0303005080004101712000751004043d500007101710b031004000824604080c145e00080039072144114240180da5416415248122408240100e015407403140603034503a264000c1005100850000e80000c4905190652101015a0b85101103601e1820100410061407039000100c3e80c3c1c09c1c40074003c54000c00303581c08590001000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 952792841 1250 952791591 952791601
    0x40c020a0305190e0909010212010807060516020307030605070c140307030c0311280213140105060f0f030a0603050f07061b060213090504031d0105040e07030e060403110114 76
    0x44403c403a2800f000c0c54440c110190814825611030542ca50301c40d0307000182c1e00401814550543c007401341c840c82000060000d0745c0e28004980c80b00128080c01c3c001a41c100138161180c00303041c0c0c4d083d04461018041361440c0c4d03500c2d1614030031248107480100000b6101000d002c140010041000c0303641d001c00d070185103400c038269009001c0080041c03009043c0021310800d90480700091203071070104120320001988400e82c004010380b00d000850000c902c60042e02d440308d01c1e00401482080d01c0b00c003406a011340c0c0c07a400c1608006454111a042d8040f0341010000b2020801c0600080c1d40150b1000d00003040080c00c0d458142c4c144050140d900c044c0d5030003da81000b046900c141001c22152607600420003503030315424820064440d81c1071100b600003084400290b049620744c0300d41d100d64001d03503c1610040340d41c5041078100d5003200c05540081c006100601c4008481c1c000c0503004981070400017501c0303840420140c1485400c0f0340580100d0070441d104c100c450400c3c0030b01961a60700d003442045600c2c00c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 952794091 1250 952792841 952792847
    0x4050f0705100305180601081e0c060711060403300e09010303031a0904080d06080d0207051e09070818010e07121a09010902040c03060503030a030905010204091406040c020a03 77
    0x3000d001c001055141e201086203a0101103e480178921040d00752030880d0784078119181ea843c41c5030a94440711003006100100070300040b40c03000240c40700600d032506d441e1040e03d900690a440c41061079205504200001c005100034402c80c00001c0f45250703c1051216609100603d50309407200c141c1440081c5982109035030781c04d62014152a4541400251003408012030b4420101a201080d08000e80605000a120018005d0b11607000a038006200c0f003901d0303135001078076455009446000b5a01c80c410900040c81c00580007040b440c40c2030000c0310000741e20f50001e9820311041d10a00003041000050080148240303004001e0b01100c440240648400c14040c0d5580300c0e21132260340e140b600c0781000c160410118810b02e11010100c2450050b25051025605000f46850001240304902c0c00c41d02d0f010007802130040da0f0440303c0083c061410904418010381c05811031402c00c03502950308010108454100740724503810245c4c50300d100c9807503250440c203000807103800e800400c05640c0100d0807e000664 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 952795341 1250 952794091 952794109
    0xf0f0305040201121a1e030105090c10080916030305180109051c0503070605090601080c040c0909020a0315090c03141614070209011202011206080709090503130e04050f0705 76
    0x40d114000909139110084c64090380003500c0c3c000c0c6d070002c0240b215050f40d45900200804040d400c900803c0704d5291040798650f2001c2001d6080e8102d0110007400e0309140c0501c0706558401c034000f0a0b24500108102c000031003c1c401d40048011600124450300b002c482c0d00f20055081c40700b0b003444584242090001405280d1441a480c140b05941c00c401c81040000c2c415a042d04c0d5001009104a0400819854440e1424040c2a10714407508800650b545454001c2c584081380c1515424509030500c0d443c0b6001e58008841e600a0548030307101505a03040b0b1400f00701c010181c3c9203000500841d0213400030159600c00b584203000040e11014401190001030405202660718141191400649000c082140c0244407020b588441d00100005420365010b40e03c1000ca8800d07660b0742d403030050052460044681600030010240d026090a0207040c0196218203079040c010700440f400c1a00c07903041050052540d0b0046030364003417407800384010814200a41032405407404040c1030700d80c0c105000308113540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 952796591 1250 952795341 952795367
    0x1b05041e0b161a0103080705060a05151c020901080616030b06190c050129030307050d0e010c1401150602030f09040915020c0a2607060504210f0f0305040201 69
    0x2104811000c810040080c0903144000f60034a824056980c1d24209561030350404002520746008000c0000c5202e52a48281d13486201080c1c50149400d0094050100181031500c1ca0a0087d1144409070003507502c4400340e5000744640c0e03008004506c0d02c00c80040e0085503d454803018076003450003c6e04142d49003c291112904401014803e00482c88400c803101000240c1c00f50031946401d051801c596295040c400342c2c0030804001e0032201c0e418005051780c0b4030602c2d10107440f542281840390440c9100e003181c031400000514000c40004801d40b00c0c58003c02c00b10280c040d0981d545c178420500e050b60340c0c20f810300510050014505062210040001c54403401007401c1c03040d030303441e90000704110702500d50800286403103104544950310080016603905c1d072131205850061002c0c40070085044518040f0481403c0c1164007404c148960703032804050701016200301d540e0310303a00c0c0b1880c0100350150824100d03219903980761841041c010344054020300500e10f280d001c05040c80c0070080942d070404803403030000d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 952797841 1250 952796591 952796617
    0x90f120905060417160306050411180406051b0d0b090106110318030a062405040606090e040c0302030f03040608150a0b1309020414041d06040b0a1b05041e0b 69
    0x121202c901960418450a81e0071710401244600401070040700ea00c2680304a109590102002c7d105004000c031207501001c01c103a104a0030303000140040e00a822a80d00800740c5400c3d081118510700060180e50401d1441c004030907a1003d240001c0d01c1c10811079801403440c0d00b4081c402042a100441d220b10030701da10310311240400c228000e51074808001025031943c0040701080440c039010350096040c02405030041000d0f21203c00442e5500e46441400101d600745d4403aa07980c2403400c56988400c0900400903240b10011101c0000561020f00c054207002e905a0040c55489050030070160941300e018100721109410b0003191006501ca400c4000306030350310704841702d4541d0310403003441d0044e5005402900030703d0300100700010021215004441c1400040303800344554490796648003501241e81641c008140c3c030280114002c10310f0050b14076002240f251020070144851140c6007141900e4a4500000850014003003000041000006c081c11001d10040709030185044400c1d00640030b400300448070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 952799091 1250 952797841 952797869
    0xb0a081807120f0503120601110c03030a030b0d0204090308040320071202031606050c1203061503041a04080a08130c03120216090914070b270301090f1209050604 71
    0x2d110b28a43c00d0b020055010b4100d9075a84c49000317030511b507601d082d141140445c2402c1030030102c40401141d0010780341c0e80030f070066044c0201400101c000c0c15101c00d650360040620180d40015031940d00580c41018060b40f01c00585080601c3c000701618260008140c2c21484007040b2144001c0100324034044482c40c1d501420040017030300010b41041c92489107000e101601540c0064081e4000c00501580700c400000e413604542000c0c00007100e440101d480a6102e001c26101071302c071280400207550054050010056059048004015400d0056409544d10381010420b01c2c1d12036444005550303c412200100c3e0640d445540c0c640c1961071503070000a04a007010194000118801c10409401d490300c0c4036111522940ca441d90001403507001d8055440d040c106110800507000042d4202c21698449140d07407800200c119501d4900d8029030b880c00c8000300841030300466a50901030145c0480c010540314566090528010400c82848000300e818880b0303d240070455692035000f95021280c07005802c0746 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 952800341 1250 952799091 952799093
    0x50601030209100f0e100801051c0c1805152d183106020a020705090f0a0b100f03050405120712090801020304081602011202040b0a08180712 62
    0x10190103806100d40c1c110f0700988407040060351020115505090580312510100c20280c00c2c08002e00303c240a20010841c1d1000401c101e05281d17518a070004401240340f66000703c2e95451110a03e00b5034032102030840c28801102640a952085903045003504e48045d0498080c0000b0914105590703a0862000e61401c0049810ba000001c0116040400414160080100080b00c000c00318080d01d6804000c0403250329220031941c00c00d0001e000d00000c9003c040014040e40e20600694011347d140c00840c010b4450008980c0c6840b400076015002c60140341e02c0601e04600c85100f103404220800d4803868120f43e109140507040b8030000325000e200c2ca00400d02e0398590401034903010308525221640b0300005a40d6003446800d40524416100551f01c0c00c1c1c1007640c07002064243d010960b800f4000f10401c00080d410b031000030702c030070861034410b0501c0a0401040950071040343c2107039100d910306031000281c00d50007a40c00746449510594500300b100c0004940c1000340c0c4c1c0c40442e4080d880703c500c01030300094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 952801591 1250 952800341 952800347
    0xf0a0302272203180f0b1b010c0c0b1b16020f18010627080a02030f0c030706030914060a0b1003060b0306040903050d0c0201021207050712120e010609092d0204050601 73
    0x1c01608010140e11002070b46c5400c600c4040d440410301203c0c002001100301b060150600a078402000079075030f0700d4900c40c1c85032600100200050040042c00b1020510600c5404121020b40f04014121079440d9021560307006100c144048800f00718415003d4184a0400d075060a0380310341514218a0040f0283c2510b40c0b00900c60603581d04501c1400601950001e0001c0001842e005034500c2070b019a0440748041194568500d94002080d6054006502c1403140c644a0350000320140d0040e0b45403c2d5084c04080100e0900d03105581050110707440d40384503015820b00f222803000c110042d1404005440c0380254640444c01b000d41000d100d035445204840515104606486d949030000a0400841c1c4007444064007d6122404022841464400251a09014400ba00e490541002101640c0e9446040c2240ca581c002e0b40441d86150340d469550120314024440c10010342103204c0005043e07101400c14400b0981c102890354008002c1140440c02c68642c0c5240c00815031b81501d011410340c0f00c0400603 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 952802841 1250 952801591 952801637
    0x120f15100305030c100b15191707080907080c0d15090c0f030b0c0a050d0c0201060803070b01030b0c070201021b030109020405040b040b160504050f0a0302272203 71
    0x80e08521000c03c03061a1301c04003194004005201c120104001e85c043c0d000d1000c01c0c00c2145078018135000a01c00c5800c2a01c03150802c0203594a01c0c80e240d80b184c0b5040740380340000307070041d24003400003041c0f8000c0040007101084003401400e070342e100401c07441c05614001140e1103c089002064170082c5580c620940c5800c0d00101c008a604c080d1140500b500e030202134404150510065440901010100d100821800101c4036100419580d5034030384501c4015000280803140007810466603a4000000c03510b1040c005000841d10543c8000c4503135266041400c01d034000a00248c6440ea0300300035001c0140c1c0c000900e04000c0060300c5808008031001e80009004150344c14020350007508100802c8104071007054510300c40ea20414540000351641119600d0a8030010200340200300104030500240c0b81c0441c50300004000246880c0c00310f5240c0d40460502e843c4506c0b50f86800040700c8045101141405403e0b230301007550b41c500101c1c0301e54016074500d0b03440c8482018050260041416201d10665914 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 952804091 1250 952802841 952802843
    0x21b0d0203121b010b090c1204020a0b0a200106050f091806040c0612050708060f040f0e030a0f08250c05071701060b031003021c0501090b06120f151003 67
    0x15548032840c41018200046103c85000c40365464142480c6030351030940d010900480900e030b81c403803c08103441600c2500c0d103030140c416a80700d02c000c000094070242c610014000d4850613a1040d07101c41d60202d90b50580404500b0410b800e90400b8002d0206884501010b10140f60032a0149815151100c1100244081c0e00c0385038100c2c06400e08000500c400705a00004884040d9960302d2a0100e190001d4111007040d5001c0d0000355400c008102c507450302d000c0e2210070b114002c20001d07074002c1c0030344545c08403400c8003445c00603900041080c0c801c56402413090001e60a03a810704400030310340700940e2520303800c0001000c17425080e4500f0806d0a64464001d0903a1b07258400c00320b8540c6611115020349820389002415034640c01c02501140c003c41702d2007134900401c2e010315010a42403c40d402c0040100c49160a64244040e00560101192090140d40300140c002c0898202904002003407103011403840b0002c0000740c3c411120491220000100c0300c1764888401500c091607103896880800349000c9a01c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 952805341 1250 952804091 952804123
    0x70c0606080312010603020313021e0d0c0503010b03030c060a0203100e0a1a040b011403090111070c06021009030816050c03070c0f05040606143016021b0d0203 70
    0x44082030400e400002400078007888040201c00c0c0c0e0740c45c07070114168801210444100e0404143d0030b401400e112905044228001c0754001c11070328050080707a080707070f403051094a08400070700303082001e4202031050440d44d20f0180e002d14030749260b000441da0384660290161258590020029400360804103240001e41a8620741000070700b0302407450b40240c43e4641c6640380301110184000301c00e18143c42202c201c4401a100c45424001507041c2543e00c0d0401000d804455485001030a41c1102810081c008288034180101c680390401030003d29040303035940d1f0b0f610194500058400440d81007031007643e20140c4d08100c9540300c070b5003000c1203c0c940210320000b8550701c004982003041000c481400420398a82c00380100340d140da41c03000c104c140d070f5880c456072010410303489296000410303100060007000a40310341c000c040d040491408035010200324910480c42c1c40c039020710204209491000060456600c010000c0300a41a04503242c0c00806e4860307445204911a1001151800d102c0f488810030040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 952806591 1250 952805341 952805351
    0xa14060904090311100510051e031912050301050901120c230f100801061409220b010801030c0b1b1e070608070f0507060f06290304020f09070c06 64
    0x3ca009441940780c0b0078512403d0140304118038401d030040c81614410510300b000c5400c0c60340360006000002e148241408800c00c10240340302c100303840800905107100e1607442440710760841400e01007044407004d191102040302c1000100916614004802e05507000e0701c050585101c0740345000741d145d06040c0c0c0328045801c0e1900d058240032143d504445c000d000b0a80b21940c00c0103183c4200507803004001742220214810000611000388510160002c48800d400a103160240e41300000b04041c5420b841840170540390342c40e426010a0700e020300c0e0096002800c100c0001d50455445200c0c5d20f665000748110b001d801306100c00c540c1006001c0300c0d0311161400c2920301800507400c1e48160320040c2115504030f8403410fa0700041042c440c583c101e115901598682c4c00304a24240210390b030b54031605c005d0761526200c8020f400b01da0124480d61008250540c0000600ca100c1c010b403019a1140d140d019070914814000c020143e20b42c508100c150083c100c07030070805035403018015956891407903800342c0024a81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 952807841 1250 952806591 952806593
    0x3020a020f1209040c050f03070e210a0c090b0a0b1c060e040302010c1103030a0c0e032b0906020606060d110301030812060604030f24020d091e020a1406090409 70
    0x32000030002c22000f0307a8107010300383c01c00034203964070720030110160311281f4100300081c901d610900182e00b241400420000e112241c00f440020859000c00941e269504074008090030000c102030040c009280211091050103180303400501404014421840b40000c00640c9040138580110172010781d207413000b010041d03123460300340201c61440c1c2103604501640ca8903c0310214140191a51a0404080c000440c83d590f81d0f0140c070307805401c5040741c041c180000080d0044503a50b043c811007008240c1c0003c500c805c88080d800c0344410010365052034090016181090001c60790129080e5481401925506c1d5152103080210000b0310442041d8640704401200210403c0254002010103010f29489202e41d81c580c2010071141e807040c0e2000404a07100f8071400c40028510036180b500b01c084608228014002c0c880e8030340141c0c3d0120180d9044143e44960380c0003000400342c0111220003070044451902e040ea680402c00c52180c03400341e00b40540900c010800c0555070402122050180031304107101a41035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 952809091 1250 952807841 952807873
    0x7231c0f050108060f04080d06170307022112250c151b14100c0918200309010e010c03060302011d03030d0903020a021005130e0c090103020a020f 64
    0x400600c014a040c2450000100b1a00020384240038a03c8820743c080513480760342c0c44100560180da0800c00a6449000026600105201c508135800b021000f9594484042c8104428201031030406010700c0d0300b0143d2010310090005001e419030302c0d80010300b030b40c80d072161078181c050800c0b40c074802d40150707042c0d641c1d5420084e04040740c0342100d01024603190900b2a4880c2030314125403000e0250400020201c012010810121000b080c0d10056015143c01004000180096459611103000840d050309010050616403424508109100840801c6603400a41403a03855420940c2e8408101e9000300c0842c004c2c5400f94000264410035038001c20501440c40005400f0305540d2200382d0104880f00480c40783e05032120f410300f14a0301c001303003c1d5140011311a41c64009001c2d9200640c11842001381c20740058545464401c103285480c1c80b83d913140c242103403114121810340d80048101c20703c0d80301442a1900c501d826500515001d09001d0789800c0d104108910304500c44e60a1542e5100f0b0303180700914034031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 952810341 1250 952809091 952809101
    0x4030836160f060c02010e060904150602121c0506060c01050115030501050f1012021303050715050705060f0a02190c0302160305070e040204020c06010602060a05010e07231c 76
    0x4101420307080c00320307030311080e103202201c541c4907500c08100030143c0000158407a001526000200a082c2e90038005190b010900300d40c2c00c80011401a46201c205000d00d540400800d0245401d00516510340f9840601c185800d0040216804100c2e4886003c202301d55158016a12000303100ca008001d62b40e502e41a01c804600c2c60104100800e141c01d00203e140d0409841c08072000401424040c58090707a29000c039003154078003c3c1b0075640d80d403d1044580302c2d18005005c00040d4061001011960705001c8845a1f84100e204100240501040070300c0000314081001c135031240f1605001185070780c0d4801c1800281c400c81c103015030044c0000100e100103603003000603100514069800c0710350380c04000e81e071210010040c0c000600140d1140c9400c02980d00a012515441071000c4e20150510f884200c00b140350600a80011025810007410408030b0850b0384540b42c014a00d4076100071240c00d108d8405041004040604070350703029201e446000f842d80c0901280d4100c074142c0c21101c0128515904800144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 952811591 1250 952810341 952810363
    0x1a180411060a0f0e1504081c03090512030411040f0e0c030609070504110405100528051603090f080a020102070f0602031b070e0406061d04030836 64
    0x18090340c1000018280701d0300352090309100e42c4804102c41000d203c291001c80c451300c08181d00107240303203002c0c2c18a421000034000400c03030003004220078a2071080000411104d03901c601e0415251030720031800700e54000f07a8000b042d0800c5240e55a251601d08003000e400e11240f42180d0017900341141c8914210b0954440c1800c40c1d02c40d401e03a952001502e04040d1514029100d040090340008001c0c00700e46000e0303006480c80707104090380c41e2501e0f5031a8081201d600d05a64040045000464944116803440c074a40040020040d011580c58500b0300b0043d2141c024074203000030347c0d0341c0f80c040d8408041c09134201e10013410311101d41c00c0d0304e2076403552501d9841c011060224014010310700002500740030284400b06460282c0c01071410708085c2d8003403400b44809940c100c0c43d82e02c2400300000b51200601c0c2580d003d5409000d000c0341d0715061038100e4031000d040b8541c40c03210a00340e40400000c298400d0005401c03100003090300c880d00c0c12601944c200322610540b403144200000030380086042001502c2e907844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 952812841 1250 952811591 952811603
    0x1021e18300a02010816210e100603030c0314070c140f040203010f0621060905010306230403120221090f0f0303070807090e1602100c0903061a1804 65
    0x1120740107004988031400124000d000c25843d03c089404451040141d07a01c18506140c40c4100281007914020060000300b108850f4665840021030600340500480d0323408592102c0a10100b891030741d004010341c80300440507041009075903054a2541d0000115448181c21150403803950303880b0343e05485484680d4184500ca07140c8540b2013846400c1c00c0c02684d04a0f108054072000d03507450680107540720307418482500d1b1440801c3c0e00c810080c150034824040034045e201c000103203560541c64041300312804030300c10001c201c4000b0b8511055440006000c4d40c09541840d10850300501701c903648000c4c0c09502c5540c0041905040c000c400d0000c401320803480340c01350004455160558004140d103800485d031410364590001c00000d1051400b035000c0340e400c10007615100204542e81c0110340d450b10002c0c3c5058151036201d00030400280d504000d2440c0b0b094040d071041042c01c1c0c3c89403002d8030310809880018001c40d1501c40e4030401c640070701420b4040b000040c010380503000041c00c200380250390448040300e41e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 952814091 1250 952812841 952812919
    0x212150105010c021f050912010c231606020f070629100c0f240e010e0304120f0206070b010905070516020402070609021302120901021e18 61
    0x565845440300c280f07a5a0041d0004410320b02518040c80d0880005403940c091101c200200c40958031101c0000000348401d00001030700b0485040b0080c08150002d0b4840b01542c1c010000003076011000084070098080d03800b684100413030341c4c134051010b80220320300c1d2006030001044010501001e908807000b00c1a0001002c40700d102070200303a4810f030210302e4000d5080328401c2e2080403d90300520311700100314085e90804420310040e583c1c45a0380b584030981e402007442c3c1c55150300020341c218080d403620318954000074000c005201519030782d42c1c0074a2190315803007001140d48409002e011202001c3c00d0360080d01450f44e40321282800c500340c103028454a01898940301c0000c0b040c034030501c151040e698002c00c01c01001b00e40fa03000c00003e500f00a00c203071080c59440c0c12110041c1e680010304002c2d00e98503440136850720480c05050120103001016404580d00400010079201154690ba036098000d5602058403403c200250340c440115001c0c0013030f00100d1441052045407480e40710082103034052542025 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 952815341 1250 952814091 952814099
    0xb0a020f06091504120504030510060510090524070605161803022d031c230403080f0c101e0b0112050a020903060c07020405010b0703020307030e010c02121501 70
    0x1d0b85080c0524645202e5480d0700c08940045c4c1c0780034400412100901c1c12a043c81d8503502c03040c0c1410000011099030680c1e40600708060301b000261388040c1c0140341020411585010007042000200e50801162501c0c01888440c0800c04a420790b880c05400100402142ca0701401c00e01e5010716841e03940700032070b8030441844100c8041c00f012500741c940c0601941400c04103000c1200c02d411084e4402210601301c224400e060341c60403c001c00c01c00b404000580c01030340017110098030030b080c1d0104500c00d24140c0705083c6d15000d112030803101180d078810000ca03500d11004c400002c10380501d180710480d900038041003c803c4206504080702d43e040f01300d80d4080000c07030284040200d43c0000c01e490b001c41c8421008a14207041603020300d0740484209805071074814072800107400c052048810800e051004600da0301941410b220f00c60240201d441101c1c0391071820744005c1e50f0b034018240020108540c80441c1140c1da4420414000b84035809001c035514280810a40c87d1211351a844050903940c100380001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 952816591 1250 952815341 952815343
    0x10030e12071b0e0405120306010908010510091d1203060316271a010e0a0b0f03010e07080106020a0b10030b0403260705070308151216050f090f060102070b0a020f0609 73
    0x13070241e40c0c000005d11220b52811501030064000500703240c1840780c00d0750300141d910002c1c02814411095000301c1340e411410061181c044650010700c400c001b07004070410112190000941c1150b003905030101d5610380c0d980030002454141c170700d102011101c1c03402100240b10304008150185804c03100182e20007050301a0744240454403005100c5c003958a2241e02a15154003401500082c000040c0590241e1511549581e03c568032004010080b080004010440c40481400032500f040c40762501e66615403410030002d544a0900001401c90008000480d50b4040e99082d20780041d50301040072212071400b8180640400c00045460010240552170555801035618045105108507150309081c0000c54500700c981d644001c00d2055031602c2d8840500c52541d4082d088002c0c0c0700500c0050031a41002a4401060001e50707114500500c03103d60025101d80d07404000b55032003200f00301000c600b9034840004034900310b107079842540c1d048000500d02800d0b42e030200b0194035425141c1d0840b0384e983c035280780c22 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 952817841 1250 952816591 952816619
    0x150303190c0f2a0f1214030d0f090b0a0b100c080d02130515040b040b0304061d1b01110703030e060705030c011e090210030e12071b 58
    0x245080c00d6005550031091402400d0400c050350048060807280b5102d0307626410101468a11100322501814284481411000802028005a102e1182c840385001e80840c80d8400014000344031039008109015007400030001d445000c81031800900940d01c08a00c1240100007042c0d05944985010000800424035802041c0080704090b00c1386003001308002080f0381e80b51b58a9002c43c0c2d482c004001088210805001903d1003024000d034040b800d620b40410001c00303d407805003085a0010500080180e0181c0d0343c15242140c0100201d40c0c0d40396950b2511000900d6051090318040098040001e00c800000902c80c2100011044106e8030b08480c400540c0c4901210b14079948981c043c640900019104d1259202e2015024004a0800b4502e588050a5400c020544000c40c2e41d42d042c4914003100c0001d03400e880b0105810704001c10120313900429a000c081e41e0042c800c0c503449002c7c603e8800820070006503134160044c3d1054841a40f460890340070611078005003023502a074000443c441c00700441c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 952819091 1250 952817841 952817857
    0x50301050a050d0b180f060f060102070f06050304080f0d0207030e19050306060d0516030b07030c0806030a021e0406080c09010815040b1009021903060f050a0b0315120303150303 78
    0x202c040744d55500300140c0742c54402820340c8890b130302400e40c00b0381010904100803401200691840fa060f0324241d000203181180503030205038a1400c0032400c10003642c03c0800c5070b411030341040500e940c41028504040303d03449a420710030b14441c8002489c50515030b02c00e044501001c41261041c40464180042c038040f560940103541c0c0c0341d0003203c04542245000078508a600c2e00c100140c2d112506040101003008440342e100b0f54038141c0a500300108190305200700900224a82044140b03420f003180426555940104000c1c0560000d090b007104207c8049885084148010030074080c40b900d404007e41c40b1407410047c2d601078801c80340046070941c00400c0c2170076000303035940515040c1c0d030740c07a00d8406100c0000b4080340c0980051280c0800c0844181c0010710001070707010703040410120031000c01400c65200b5403182c4035107030006c101402156161081c060403280110b021503202c0d00c1300030f2449404140c1454590303204522080c54803580070003101440c4126101c1500907076a90b0380c001495280d11032a00303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 952820341 1250 952819091 952819103
    0x405070b0a12050603010f0212070e0d0309090905010b13061a0424050f0d0501170d120c03060504090b01030c060512070309150c021b19050d0f12050301050a050d 71
    0x440161a000682c42558442e1000700003158407500050000700326807140140e828141c00d03103410441cac603980000264070070510170b64112841000315100100324400c42c2c05410415074494003500c0620200350030050684d4002050800d6007039502c00310200420b0244500101e9503460b138500c1d009031007035401b954121688103d42e450441c407011080200c0b044221120820700c8414030136502c02400f00d10161110719542440081c05504060301558000d0a01d00020703019800240d01c8900c0c1c0c1d91008200035411082d810101e036406a050040d4040c0016401c5140c00910304580c2005100e02e2051041c12a0302942030800f03d107844503000c40d801d01c180040c00c841090f0342c030b020a50359403090344000d1000780252030003c0e402e88010b5074101518450601c6c240180d20424040da0b15134040c0f0340244008070105c0c0c540241002410014100341024480e45220321810245201800b101c40c0384d0085c001e601126402140c1d0440c440038005400a0056a000c0e41c804071001c112420001c0304141182e400038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 952821591 1250 952820341 952820357
    0x50106180905060a060323070903060e010507120c0c02060705100509031306120b12070807050402180d032d08071103071101090f080c030c1c030503040f0b010e0405070b0a 75
    0x805901138000301a64010701d60207c80e40f000c05a840011450080a943d92003582c1e0a285003803860a580107844c1c40c40507a40752006112134590401e201c0307015030340c3c1d8440120300201c10075401c2e541864800e07400781d0054000500101000f80214199076210110782040100c0c0d229070f216643c0c0c90048108010603046080c0f07040c00300c10301880c2c1800b81d40c1c2800c2c0c8041890350408002c18480203444174440010b030f025140621100ca0140200c402a000a46045003400c0000c000e548441d10555072050047d540c60700d0744424035204426401500f903140c03000038104004000c4407442c02d04107110034400614540c000c0362915104841012016900310011170500c41e071030b126a42c1c0b00c02d03030440c2241407042c0c0110004080d0001a2054002c2a420014040820062080c9801c1002040c1410302c161030150b0101c642d001040030401e0450b4140c98134a884c1e0360303146072804514000807800b50000349014000a0100300041107588078030312030002d03102955070795204d241140c00380f207210f0710201c1c120f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 952822841 1250 952821591 952821599
    0x70207060305040c090903030209031002090f0f04020c01020c0a0317060a06120906060b0c06130203210c010207121107030b220b090d08010e0f01030b0a0f050106180905060a 76
    0x40d40000f034205001e22050306a9540d40c485030380c221005400d0480200750081112002460f00340240c9041003051241545040130305030000d00202e0614881e10310a403515000e101c4540c5036076041d0f90110410307000171980c03403494032944c5a503a81941c80c11030006a0301380882c060b12070b016500c0e502862003c2c2480400505001055030603203221070511102507590b040303010108042e80502d100525824107142e6a460000c0003050501e403005200b0344400d803081800b00300503180040c504003040c0810b030f13a411002120303070720140e0603204200000c14158004100340342070120b0040c6000f103800441c0c5035000e0a052464030261165650b00c40a41540610301c0021704502001e01c032044500f2100c529562030241950b100351b46843c007507403500c030143d00c546c2c010311901d500b065505014012280d0700044501c3c00200b8000f03540130500008040340790200101c1c01d8038045802951100e28240801d1140d51f840d0030300103002440140d038146240062040009811405105883c06490301806103c4c6050070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 952824091 1250 952822841 952822847
    0x207060516020f191a030408090405040206040e0a05011706130201080615030406050106020d3e010207120305060a140d0804181b0f0c0f140d2607020706 67
    0x1506020b0303070801c00c054005030440e0703030745401914a80c40000f0b03090405810900b21007440d402e200b0140100090400501c40420100400e45101807030469010901e5651440031502600603a480f80c0c400154400c2400358907181a001103040c3d178a562258081d1001c1a00d04131758a00054070600414010001d0500142d4450801203170300c0390010b4190b0300c80a5880c1403282450f4070465082da070722507a4100500141d5414050f28541c0c0c4440d16054030804800d0903000481105c110001f50706180007000c2007840c071840b4007481d40b9407240784000c6480e8145070070904440d0960025101c0024a8840084c1c0a40341500c0e05009690108000f2038065102c40188142e070016038000780c4030035500388000209401e4020018034000d6400e4004681410b041c014845858041b0340c03058140040c030500c0110007a40001142e4107281c20a17117140003e5150b051201410740c0c600c1c01d078056400f82c58450701c02e090f0045a4480c000345070161080e00f050382c18005041540c0c0c00e80718140160030400c010012184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 952825341 1250 952824091 952824127
    0x7050403080711010522030c060804151503021f02160b0a0e030f070f18063015090308010807030507050904031e0801050310110a030e0708060403170702070605 70
    0xc0181441440e00110303110103caa411111031b02401e2041e5400300344100300e01050040700815260901b0202420143d96070b0714200b0505103081406070366410239a00c055800c10f40f1900440d000b40290b40040b21a105140e0094241c000c49000340c4103074284000c084519208040171030340c021250700c0c1401e502d4842200c2e038400a00b4065414421602c0f00280240140f081d90020b2403c0035544031914a40030b0114070016203d1107440c40c903482d20001300881007042032140d5500302c040c485c0b400300c030080982d200c03c0b181c92040060201410891010300f0346045900007481030f4000e48448210342ea0740e1580d241c0c1c0d111540001042500103803c1041175040c00c0c400240c0042c82070400401c1012103492002c00010a900c0040c002003102004004a080c14000b0185600d0600f0f42403200070806106021b03184100ca08072001c0503551004982d03104020700c0040d014000030400d0700d03a241003a00300102500f068412444190301e40e2404500d01c1400000c407041100e00c5600d805080c0009241c00c400c0d800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 952826591 1250 952825341 952825373
    0x2d0901180c0e0a0f0611030f16080d060b03060a1a04140607050105040c180c0e0f030f01181e030801061b02041b02070609030305040b030a06080f0d020105070504030807 74
    0x1c141c8070582d2807140e4400f20440f010304411814407056a00c0c1030001030107030a421642c024180c200300401200042e11a044a00107040742102e801e032540d46103000c0026100e60148172017007034a05440454041501c03001507000f02070840366401010340b02d4403060800c1c0781b0601b000c4020300b01000200304d9900d0340903103a01400d800406060621116448180c02d6910071501110070030390348001031202e0014407007115001440340c40100510410301c07c0c041d2000100c3c0e070305a88191070b00840e86d503441d034040202c0b003d0f91130fa030b0000744540c44803003444440d80310388028101c9004000301c004001c03910120f03400702c81c40764055456110a91a0040c1030302c0f03c0000c40c8103d001e60401d070b00301c2400340e01c0310301544503560303030041081f0812a0680d40007410302e0001d0f0401010000d00306020000f20b1f0b40310040d102515400c1c00c1a0365070751541250b2500074401130340441454021540701c0d05070014041101c1181c42030f20b400034029661642e500300d409200e04d000041143c94140300480125000b4042c0b01526 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 952827841 1250 952826591 952826597
    0x102030c07290c0a0302011104051809010b0315101710020a18030b06041505130209040612080c060106080f070e0f06132c04080a0e2d0901180c 63
    0xa000d42d058019400300002d62420b52004a030710f000c15509116180e032090048840904103800e110001e40b22007800400d0002000003500819000207080d4000d91500000400b1264445080712208940174000c6521203003054820380b0000300c0040c50883d40c1000722500000e040f207410000c502c0c00003500206c6090f010000c0c10043c00701c0701070b41420203a0203180158444991454184104420703201200200c10011131855401c00240d01d80c0026000f01c041d1040b80982c84252035400b280c02800564451781915050b11408418040c0940041240010300800d41e2026a268102502c21540a0b00c043d25041e40305400190001c0c4038203201401c10301c008150140c40d418100002d05980c00c606003018501008103801c11030300c602c040340c0c100204c842e05100607125643c6124105000401400504000000550f6030300b46803140580e00141d806c020001c41c2d21410142c0d0b20300c6085540d00c10308130509108800c0c401103113004054a0f041b10b2500301c0c6000c2d0f016940700050302500c1d000300c0c20b000f4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 952829091 1250 952827841 952827899
    0x20d030c030c080708090906192304141e06011b05100c02060105102f190501051e040c05040e031c14062e05360102030c07 54
    0xf400ca0008101c81c0d8001e5114980f034059110410108000103041e05101c5d0340c401003c400c145c031000301150125003500e94a12800c0e070f40c00300070b103190064003495907600500c2c1024036100880302c901d4140c042e0181660450380280001540e050b2903c0545a9070f001c2000e40e07900d81c40d5550340248019250344103509442100c801031001c4800d0b603c401d100e400150300600014019030070907142270314400c11280ba10043e02560446540c60499214080740090b81c21908900724414041000c1c900d40404800c00315594886824511f0003440c05070f8011160428016502c030718440080700060140340c11440101c0030520384130401c002028004140c9100d400144844440c100e0504d42d546e180400702000410112405c0120450165000704803c0c4160040c0701d080824600c0a00e142022442d9501c1c0c1c5104082400001c0c2c1f0240500309a154001146502144034400c600c2107000740025000d000d003144201203001079869014070303508450301c0e501c40c6a0810400e030501c010542079401c0c102103664 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 952830341 1250 952829091 952829093
    0x602150c070803190905010c12060609050f120f010b1e0603150406151e02011b0e04090b240f03250803030403051c0501060e0108070314090c120109020d030c030c 71
    0x6071783d2a00c8040e21580d54980701d400490380c102201d21140b2098140400000c0e0909001900e24031507400742d5400b40903544060384e00c40c0c0710b1207404079041002c1c0b001c8420481d03601c0240c9000e01840304d8802e02070b0404001d2038400d2802166070001901c0010080c60a540c2e81c038180b0031010740c6600c1c01940c02340e00c400d03000584032000d1001c09544200740c1d44040c840c4072010145101d03a8000039203001160316180080c08159940c0410035040340040c0303003083c00c0804900004015040800018000c100c00b881031220f110060190a405030318440b86105500e0540d01c1000340d10f1002500710358040e0058009030320071803100440c00d03100940044042014540f00c2c0042855500112011400725a0008014101d000c0490b641801e51031815001d00c440d60500c40c00a294920101d24036060026160100b0310340c278081c0d0814445142e10000d42c0340070303203070035000a03070740c0c1b9091a2001d00410034100c581c101c6147c1070040e181c1c2640c001d8400c1035040440e82d82196403074201c0b42e0550801c00e801c11028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 952831591 1250 952830341 952830391
    0x1030b040f110702012604020d03090b0f091f08131704090c0215060a05040905012a0f0302031e06030708060a1d0a030801150e060d05010602150c070803 67
    0x180a0440d400b26848020b07910003d045100400000c11050f5000949203010100302200a58001e6059520301c104a695143c1614a8642c3c1e4000e1f00041c4c2c004591661041643c10280451800403542d015103424078000c10300301400240c942c0c3c4000798506000400000d114222120824860880c81070650f503001060010380d007294021400132900c070400070070060390420050784012003400f02d40805d818480300060041500c3e00c5801d004907221400364081c82400c4d44803240050074151101c103281c48030002c2805031041021581c000c22481c4241c080040d22070f209882c807c80100400d15041c4041c1c070368180c80124000c0142d5494404c040d0040358880d8113028050080c0e1361400d02007005522500b0b540140c2c0c00450440c02c0b564400c88105022030340c8140210b0441d04116002e814503452403200f25080d10b090090141c102c0c500295181c2d000050740d101e94100c80c01c40c3e094a60362100c0c1e03141c400700000f0984402144110500858000c540f00900454000048503c42d65401c0d417022149 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 952832841 1250 952831591 952831601
    0xa020303040e0708090601061b0609021e030609030a0903110d0203030403080306154012051c02030f090103020d0603050a03031419090c0305120c01150506030601030b040f 75
    0xa40080001000744403c00b90000a80d50b0809441c80c0900055810024010a0342000e816246010380b0032103c1d02090129503400310040b01e030040d04d400140c2c02d60030031402605036010400c601038851407001840c0710f4004000c0d01c0c124110350340e90142c014619206c80c41c0741c941c0346600c15404515030201d100180c0c0c040000384000c600c98200f20f0344a1401e502006011900c420500d1020360082103c02c022894811401814070600400420750000d11464001d000c0b550405404542a00c203130f0110313002081d4003030303042c00a21810868003158211840120304d80e58013403908000d68802c2c003c904540c2c50070005400442e406140050500a801d44400159030240e030003030b9010b03013152541e01c1c10302d60300d4002e048004850f5980300b0010304043d1401861000e2054a0301c100c1c40c1e036004917204000001049100954200b400c03503c42c04102d09038002c542e4050201901598070301a070780003510b00d00100400c2251801080982565240c600640180440c512078a40c8142d54bc6c4418448508038861 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 952834091 1250 952832841 952832849
    0x5030c03190e15040501110718020d0b10090b07030e0d0320010c09091a100f020d09030f060b06130305061f0806011214070806190509060a05090a02030304 68
    0xd20100003141c001d01034000c404510140d070003820042280c0c07000b000001c0071141280c0c006e18207104800c401d207100d05c2c06c00c1240e4101134440c031004141c0e03240700c2642d0f03000b410190721f0700c02041000956060030000b02000340c651110208881d1141003100007a42c8003c0c201c514005d05000081d11041d0001881301c161041044000c030b0f0025a1803001e1804030a2581480c0310b6080c020802a000c5038006081c01100c0d22880741c4194036452015011002c101c007000803c0400b40c0f18030895081c42401801741501d00e4510750051044048010416118215078002ca07904081c50800c80300803529018090031010301c07a103806c6402002481258007060b00c5100c0218041c1025115500b400c81c850b00c1c0411030350280c09080243c4a00c10f110280c004507109044948081501807202098504031407082e0000b0101080c1c1d0141000004c8c1c6c2c004081125489074080c12038155a100c2240410422501c06a40d000b0903548248005000d403d1294003081e00a5400d0f0100c4411038200e600082c0745a00c1500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 952835341 1250 952834091 952834117
    0x120c0507060f1e0c060b060c030d060e07021c0e370b0a020714011b051f0c0f11070f0303120e01020a170402010315060c0317070f080405030c03 63
    0x18140d540e55000c00c440f000c5148161031a02102d140110042022401d4079010b80707010b5441e0742d00c1e03440da500e0a00f01e5805507000d0040c0c0b62902901480140100349a1051003441012078000802c03652012030b04070400400080c08105003010b40904480b900a901515508031700703503403240301e0008200c50020600340108003401c51411080d24803100242c040798001c149040f400e100b02d001c19500448e450043d03a00295004600c1020b0b50300495141b408034002030324406103000301c0e0b000d02c80c0220721090480010503001100001c64a401c10448910356038035000500111220b02c1040c2c0b140040c0c841403042c3d40100c0d0003190300d48554030700c0d442d101e83c4228003041400c4051003541c030041c028045d00000c118021818074070f8140f00034250100c100d0030b0050352a400030002e011a80030b64003502841d00030420b203106981d1108005040090380180c1540401c04e80300ba2007034850201310040740b042c10303130755940d09040701035070b1003070741c5c100c03000f91044540380800d1051002c6804208098901d402002d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 952836591 1250 952835341 952835357
    0xf090402031807050a080703080304050102040b040b1b1605060d0f0c020d0e030c0a1a1603081e09030a05072306270606090a0f092004020702030604120c050706 70
    0x242c1d0951426000b6400745024030b00c043e8041102d040702041000c2180d4100181e155295100d240c440c0c020710981e000b108043c44041000304500c21180b000d4082800649450125159006d52007541c5848d66940c130190030403020300074006400c041000d0702c1b681201c2c5001086003802280c0c400242c41070162006e0040e40031140c0b185207a50f101403007880811042e001b5114041075003000c25210146401411024034020262506545440e0300b00c8680901840c3c0d51035040e503d07464018180c0c1d100b0345406e1221a40030501c0c8401315070001c50343d03003d02c01582c002d5280a40500c416100b580000a003580e503101c00d4110802c1c03000c08101c0c0b007031918040c4409440c0d03501d0851801c1c00041aa101c07140140419840600914140022007a070011402c540700e40940e521034111001030030a0110354542d041c2825200c070f00b000000c4c5003100c0f10240c81030304802c0040031001400304034005c5d01c5010754954810808500400c1d1b0304490303040c505d6042c1c5000c1000e0995a02c07003074500381b041c0c0d00c0350b00025082 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 952837841 1250 952836591 952836631
    0x30d120f1d010b06041a070f0803070f1e0e040506030a02060d0b0901080a03170613151802133f050d051602090703021e07050d0c0b0406020f09040203 66
    0x83c41000f1040c002214000c0c100750030000d440e09000c80d44040303100700c0700001034288180b081c0d0302254006107900c051855503d15040800404035040340182e407001ca62044c1c17005800c01c182c8100444101c41994501841400d0103040201800000d0010340e0103026960049016031140c1d401000045889000820040404010701400080580c801907041d00940081e00010ba846000c0040c0d1b40074040b08112907844d0307000010722051104513004060b0345000c5c0b0702282a50006110012600d2130a03061146800d0705030824160701c51510007411050b5a44000e0026100c3da0280d508900070800c0039001c0a0071030086000e07400c0c4100340002d04003803044241020414100032002042507e85071a0b1b05103500010004100c07a01901d00078810694280043c0c6d503c0c1c443d034155038820b00d0384c200c9031302c141c0c0c1000620f548a900102090b0303030600403a02c0c403c01d603900030b000414003203502a420751040c0c0d490361602c0e0001d401c6842d0040a00904005040b2259118000345000d4448054000c0340b81e43c01c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 952839091 1250 952837841 952837843
    0x170114130209101a13050d0b0c0906040e070f030501140303070314090616260406121104142e180e010306060e0f061e01020708060114030d0509030d120f1d 68
    0x291b40c0603501c10800281c07000e000450b40700c000d6421074601c009046d1505444000111107000341e070414443d4030009020410a181d0000b25080d60711046e46080002da600c503d070b40300c40803010340c00b03031900340d4010040100020b10410102c01c00302c00803981e442c140042d02000a4a5078406400c1081c101080324012050100c1e907908841900390003c1005c801c80c81980007103101c0d01442c03040f0800d00a41e54014000d440c1c8503003080c010b1000c181409036440351943c030020915010414500d01030703007001806056006900303850340c5031104c0008003241c0c0c2c120481400ca074000b400340c1c06031f100d00c1d040f904001030b5031075840c1002d80690f101c2d0601007a00390500a030100c08500051107829100c882405110554841000c03a141c44030500d0b00c01c07048050310100503890203680b640144240d00c40c00c000000ea43c0c002a8100c440c1c141e0440555480e40e184900448080c040e44070b499500d0b0300550008282103024885805802e921082c003c10140d50151281d41101c0410140b00703045c0c0e1402d4141818a00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 952840341 1250 952839091 952839127
    0x6052d070b10080c0f011413180b0108040b010314030f0d05220b01050906041103040f170a020718091a07090b070510020d060b04170114130209101a 65
    0xf1810050598600b060001001010701242041c181320003020941e54407042001101e5403c1d5890240c1d48201341c0e00d400070640800c09445034020145000b42d20141c642c400e410702c9019035048280d20f040b503402c544400c0581d814202d82d5003610b1004016a03681c21100c00003520420b010000001064a4040c042c12008aa81a5035280341381c0da482188000034003050724607041d200309440682e140c0d03032048003007402040c20b250140c800007400700400c070401800e106045101481542c0060703104d40c03504011141405200c002d0405600704d403206024a5441850b40522072071112800f00d0300000c6616034148030321141c05540d60030810f1a0811044940000714103005185e006003040c6130100d20f880b89034641802c800001c0c480c607000181070303a030740d2003d40080d40940064038109950325600c41c02c0b24507044a60200140315400c0101ca440700c80d29203107001d84100001d030b90161480f02c2c20380c200094003000419507646810035117808030b075000c908841c41070700c4268510b501e50b40d02c11079500352000c02 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 952841591 1250 952840341 952840349
    0x20306010e060d030305190e03220f140105071401090b0610120509030405030304060c0c08062403070f060c02040f06060c020d050a020910051906052d070b10 69
    0x9801030a0181d5900d0744101c103c3d00e10381600d00094a5150705102d41052000c5401d025140384c200181c0b0613007684041b00404408141c14101000d9003030701d4400260028451150040342c58142c1000c0144940440e08031100c6101450510b1800446603070752401d415018102c0c6815a5503560084200941d00c80901d0b0401c108455442d81c90585060040c0520484107040b05419255808500604010002e40e005003000030300b642d03101c549070100105a1a400801550000c034110000111241c01013245401040c0f04440d07603c0003043d0803c01491b16170102580e03071b05407140000005010140e420000301402c0b295850a07402019801004142d42c1603030341080c0c1440c0780c00420070078990007042002406a040c0e03940c0f410703440682441418a4905100690845c0709001000456011958102c0544004481150000101c14105202400b06000382c0001c2802007000d09680003440c50044c508582c880901010804c410696442541010701c08458408440e01404444048400303000090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 952842841 1250 952841591 952841609
    0x50601020f1b13020d020901080a09030207060f0e090702010218040e0c09180d0905040c08060307090f090804080a260301410306011202150a05160305030402030601 72
    0x107460460700e140c40d55003810400501840c0d280c0e03540c1894a038400c025142c000100021034680c510007441c40041e5100d84441030004501500052080000740309650203560554000c0c8072450030500140c0d0b020890207d041c00f40106d1045c500380c1c940d40c8aa00c14031842d02913001688440b00c0c240014100117010703807507a20503414513014501e24000000c0c9070041150450354041c2d0381d02c980c1410a449521703a1a1410a8040c1d0501500e03020b80180030401113030340070340b010001580d4055040b00c5e00002921300b168180c1154000308002240754005528581503120300040d11402035031002c41e103502036403110145070803001075002070191454050058403051031391030b080e2411036521003800d4801402000351081100c2400324a034401e00c0310035000031044600303404000074403c03061603110340c0c4441d28510030b209050021580f10010007006050310340c040c0c699000d25202c100d00c040107400880b078503000c1160911125000842c00e95010616034001c0d2070f915541e0400c1d0041c1350400c6016041100d41d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 952844091 1250 952842841 952842853
    0x6160516030f1515060206010f050108011809021f0206100e160c0623250c02010e041b050d2f09120706030608250e0a0603021c030305060102 62
    0x2040c1252014940903030b200090070010124400c81c1801400c04e040d0074400c07180c4001000c200380c0d0300020118180c84030640c4852035166160300444441e20240594548096a80c64000f1015460780110003aa8030081603801010360381c030074403030107054200c0380c21006a001d581406075072290b441c071440c080c110740c040c070b1286454903004010400800d03112b48420018800002c40501002c3e50203111408105079101500400c200c0000801090030341d5140401c2082c0000070042000e03461059010307403003d80301c106000d0309a4006542e03802c5004803d64106845000c01c009036a00c80300b21712245485511840d4580412072041c40440b144034090b4191400f004020351041c3c1041014402e03c070b648844401d548402c00404a0240420b071141c03200240710f0714a0200c2e046425070001d40584041c5400c4401c160000390114000d0302d0043c40c1d001020131a24424840c1010b8110707003540c0421001c2c408251180d4a03800b14440005036251380700440c0c05a8401402c05901d0701416411440910003042 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 952845341 1250 952844091 952844093
    0xa0e09161a030402010c060906060605040608090f070605220803040303090602071415090a0905090f011404020103111603020a0201090806070e060a0c021302030117030c031c0b0616051603 82
    0x14075880060b1010f410f000030880c0715400c000050700419000c55004c4e20500007140d4441c1c0142c00c40d04140603010124040c0f000051111800050030700b0a018003400a10480c0c1c9001b205450650299001f181d895070102c0300c414204d0f6280601ca40100700107001941e55524500300200210071580040c811500b15240411220314a1117030050074040403560100e246030300c0301200905100e0011004d07001124460001845482948600d105000100555140f00707068804103088030380c0e029021742104041004140075500c0f0ba402040110304501d0144d181421240d9901c0000c40344000c08c400680c41104e080d400c6582c00715071500200350403002844c040c01c114501408030076102510038000e420104407103507007900c40e01d4500d00d0550050440002100f41445402c0698003d00881e90a0010780f0704400311028000210382c1d0040300780c0c01a40c1051a480e000203c81000080c1c07200d0f40c5074950b0b001244036076407a0000c0001c00c03900c00da6400e9008031464100e0402c2c2c1c45224001c1070a441540400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 952846591 1250 952845341 952845389
    0xb15150304050c131b080106120b03060a05040201090305070f06030c0503061c060225050d0507021e03212706070201030b061e120916060e0a0e0916 65
    0x8141c40004c841503400049034554140c010000c000c00e01400903c00289802d44507005003856040c5c4902c2c1d6a00700103003505c021035006071135a501c0c901d90154492b80004d0107104103070f40944d421600c14544050541d580e500c89030b15010443c0c21822014120010400410f5094814a001001141806401c61820f5400104000098102100c84040c89a481800c1100c103034115100103000350444200901804007501c404c1c000024126898410310a45011550280c0281d40b4440d500418450f19a078140a071600359000c4403a103640c02d84078450360029014903c1c19030207801408014580d890720f040c4100302c0280745030341c22100c00325102c0804d0740b6202d49030f82044524068082c2000300c0c181c1c000074042131507032049002c0d104850210180046405003018000c04055201c0c5003a480f0907119442c0054540b9036213102c048103122107000422040e405410003040140c0c00800b0082d051f5581d070b0b549002e10400312420ba509800450742c2003140100c07011000080c110180200080b40d21920b403c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 952847841 1250 952846591 952846603
    0x40b070314100e0a060b04081e0c061b07150c02130905070501140c0a03022506120911030a0c09060e1314070b072f030a060b06070b1515030405 63
    0x140701e483c900d03400050400704040d040030000f001c1e40131000c0e54869076010403e894811285a00c04030103490500c42000700310000f62004051801480c0601d40003c20f803c0c08a5401d0921501030540030316480041d000d0159130034480400c10b030780c4581041c1c10240c030411440b00c6440c040400f2031441c0541501c08034000094001c241e0744282090040607240500c402c407180035441c140c0c407080c414110709808240d404079112641041021005901407603181510001c51128000c0700000f030040f6010000a4902d5084460781c28010341001d0350800039400401c0c1808980c010070340b50650701c807008120071056440b1b000000c04070b140c80b580090500c8484c8043e03201003040c0207403000400d040c0c0c07000300842c20300c0010001d10801305400e5440c01e03a440c2404110240031021240c49402c4900a001d1130020301840c451804020090300d85035019558a4000704840302c0c2c403540001c02803265400180040308043d018010040c1c0d80e440e0350030400704104101807041d6100300d1840e410b009100004500180d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 952849091 1250 952847841 952847849
    0x60f140301020a120e03070b0103050d0908210904090503030a09260d0203060103060e1801060b071a1911071e030c060c1b030e1908030a140909040b07031410 69
    0x4120800417500302455801100740c064007602041000004003d4005900050101c0d10746910101542e580300d0580c6880850344ac828800c10760040d0740203008044002800078001c01000058850440e0b1195891500b0468000842554522242c003d12a010b000e00c001000d0b02c1c00035182540c0c5410040400d401280b118071403070340d001b00218071071303a00a42000002d4101c0c15800001460000304031a5001a15160050715510341100425035070003041c11904403e03080340031050041c1842e103450200e4980144410a4542d80070700b0075031980b000d8042e00e1803007840d0203002074440300305007040c0c1c1014441c43c1c40081490b2881498000082e00700c900c01098a402400025034140c280d082528805401001904048500c0400d1000c042d0007000b94140d05605507a10f80e141c080d042400301000105018070b0032198030500c9802c5007a80b0440115900da07122600b02c9061076100c001080c1c40000a4400b05e40c40e41c15842000000e9601d03110309051384180b40d4000b0241e0034610b1103d9103a4246010b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 952850341 1250 952849091 952849127
    0x70e0405100e0403050a11070302060306010f031d100b0d2102010b04050c0d1808041701021902033411041e061505040f09051801060f140301020a 64
    0x4005008078000301030010050503141d00450041ca06843c0c01007099000e1100701d40802c82c0301411b40d401c00000640e40c2c1c10f590303025184a15586454006480582c400c2410404041d00d4980308003514502d00e1018070307603071103007401003001c110a09003c0d400e4480340c0e010b0a002c0c91040b015403010984801310000c1180071401d080c4034002d2801c0302240904051200c0c0d80d009400e02007881808104940102104800c140e020400c1d00310741c4100380321045d0056806041c80400b4401031090342d4002c50240b07001c01561000600d02b00004d20600c00c80e80c0b050b9544805a00301003400c08404415041c416860f4141c401440c01440d40baa0032103160292016001e400d107201311400485030385a03540000742c241301c00e00303401204031031120036040501150b0240710410603c6907a0400c03898003c0c000e5800380e034a83c01c00224a6404c080d1310000410303004010a288079201d66240d41c4100c02032180e0005000241107101495040c44a40985075a0072070404e0302036841040200c079203503030009014040d100005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 952851591 1250 952850341 952850351
    0x1a0103110c0a11031005100515031308090d1a09010b10120519020730080f130209040c0806010b0906030a0c0e040f050603100606090308070203071d040317070e04 71
    0x46480d1a4170303040e0040d0000e10341018002259100e54241c0304a803000c40e040020b60400703411404d820b0000307480342c800484030040c103030b000070316000040c00b01c0810140102014103900d440d10b4150740d600b60035460704061701c0d02c180542d09500707015200c0c001c04e090304c8010a10100c2200140404541c032541e000e007540c0c40001c03440c0340481248510620b100c45d20150340f2041e25050103492458110101c501601c00003807160441c1c0d140050b02031030400b0340d0300c4a0603255660f161540c5818070042541002d07006043c2e05400603903e080c1c0d11406140280d264080e01402c00c000c0510b80070060704408103407841807185009940c1c0d0341c012260710480021000c520500003050a80d407000035a09500c0d40030303007407102c0316680703214907488240b244c00120700321001d1200c000e45000840d5160b005840028042c14000e03c0400c8041004201081c4040c0072a440b0719900c44c1c0c001c02d000c0c41c41001d20020040e0340184000c3c07580c080c0d04684000740c3d402003c00903081281009d01000e82a114040c02182c4907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 952852841 1250 952851591 952851623
    0xb0702070504020c0c1f1b050703081209010605090c041e08100207020a050a290d140103030806011707110c0a030f0b011a040b0c0a061a0103110c0a 65
    0xd111110040c10090015919206602c071101c1d2103103600303c4618014000003821500d02e10885e50fa400c001d908070f40300c0351164009481010011307610104c06582c4e51054031000000100e0203002001c4103a801d000f015120308108042d0360035188954006072190a41340f0500c90007140c007004aa0840340030046c3d68850881030902840c0104503940b0803481c0d4052800403a04004054000303094661080b00d1491b40c13980c5482c01c2096098480c0a8482c2920180b030b14198240078071103100007400000003841e0300b400340201e0740700140c81c149443c400f80e841a0000402c1015088601160030040900341090140c6590400315a04000102600100040c61240c25004034007406240359150b130181903c00c016440c1d0500135041c00c40b80d003003141c0004a00000044040c190012003401c100c00f100007030301c5c20f8a8203a1000541e00132483d0b100e258085c5030003072000107900f4416420300190a0950484202d82e910024045a10104008055110400c030980c40f0041c00310700d40c0000c661020880281e40c0301 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 952854091 1250 952852841 952852843
    0x3070315170d050a0e1f09060c080d11040f03060c120207030806221113050a0305120f09030f0c01030510050d0f052404060b04060602060f0901020c030d1b03060f030b0702 75
    0x76035400540001050006040400b035091440601b4945602d808580907035400085881c0c0fa4a0384000c0c0c1841414000b4460341c41d080e4100d019060044480c05040581320415610200707401ea00803030b8220340d40c6486080c007603000034400e581c1109041c0700311b007405e07625100036205040c01848603100d00c21005c40003500104c2081e5490140c10540400c0110900440840c200c0358001c4038405610403841030000303814030b4203501c540c0c00d8030341c0400070345180d1058070007192094001c408a9600c001c414404032a45490030004203440040c240014040d1901c244005821101c028200a480c00141c0a042c062600c505000c03801c2c01d64060a0b805400e0307003c2c141581041031075618000042c0300c5070ba06441c910000c200b85030107580074440c1001808041070401040f03031058402c000241e0003580c0001d00349003950010303640c032840041c00980b1b8107200d000d445045500c0180b01900c0540d60301c17a0440341c8054420706255402d6941810000d29040150079001c4521501c4002c3c40d592191000038404c0344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 952855341 1250 952854091 952854107
    0xf03050c010e070302030c120a060203250f14040f05090a1401030b04510c0f1101050603331005030d032d0e0303070315170d050a 57
    0x1103158000c0010500c810b184a4803009540b0040c3d10034840c1640800d11498404640446c2202010090003540311a60310000a500011324580f089988480300c42c10541d0f01390030000403088580c0e074580d148001294060301e80b4421076134044031140c0620040c481540d8881441003074490403501d1403490340e0380c00d4040000d420107040d016050003504000000f04100000c0060080d44030b01d40040c2400000651144042c8051040007401d5400f9500710344000c0c5103070344c00458140e068000c03800c4150410201c106032401d40e2242c40008050021951810754040008890503450000a016604011002030780e25655980703910540025155414170b60700fa0310740303c0c080301c0140080c401068685403003c50401e401c41d03c5118003a002d415140300000d4801e00c0b40c082000c404400100301c12010381d414003c0c1d282038200600009e90740b41002c0f407210008201035881039605907004960401c140002c0381781900c40ba400b044440d044440240407401d004203803806881e11520349141c6540d4280000c0f1020f02c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 952856591 1250 952855341 952855357
    0x20403021201051b0705030301230307080c210304062f06070f03050702070e060301090b0c0a230702010e060f0d0b030d110a0b04050c060307050408010b0d08070f0305 73
    0x240140740c24240410306400c601e1045014000e000010000440603c000d44101c400013070146e0420401031042e50382240f0342c40500e080842c0a40780d4040e404004c01c1c03500c2d8841c0c21030f600e940e110000d9800c02e440c1524081803084881c104001d41c01d402c3d40a5295680920701843e0103000c0c54510003c0c56528a500003d00850b500c141240015a00520303140c80b030506460f201d00055030419a2404580a0700800340510029070060025a1600302200100c01e40644030951654031500303a500403d58109590740202000c020a650310320705d02d540034040300c00b55160741c01c2454107550070440b0250381c901650100c40e02800c0641d443d02c160b50002c0d0581c85115140782611501052241512001d03511101c181e0760240d0880700150200c03141626481c04400704002154401c4103094001030100508030f40151083c01100c03180303090400081c8041d0411212880020b5000c00d080003010400d02440411050968403544004c1980e00c1e40005440781c1d040c054004101c0c036a144003094450784c02c5403240303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 952857841 1250 952856591 952856599
    0x10f06050d170c0a0f03031e050f181006030506160f021b0d0c1e0f18180b04030521060f040c090b18090105041103061201090803070504150c080a0e030102040302 71
    0x905d4003407038050000d01480c40c44443d00c00070080d2290003812a48074035030007548020000e80da5035407024170b450221822001d10018034092881007403140302003406880003030b51003003000c0c0c0010301d06016111503070172052803c83e04003c42d40050a96954010031b8940034204101c0826542d5012900071030f0000d804071100805044082c0c800040c81003000400e080740404800034803107039560b161190320040d01c4074081c2c0708040c0c42241c60f01a2480caa688a03550b20115521032810401c1c0310348815016200880d01039010a10000e200038152035a803c0900110b0049011240541440c40105403222b04511010740503c0c1d507138a0f040c0455015080c0540184800e41d001540d85c000000d002c150301030308200441c0283c071800004203c514241c060040403c0201a0990441d078414003041200940076141c55840d560721041e00002c01c160400031480b0750740076103030280d0b19454070050b004648440d40d01d12040048c0015948005450142100e800340c071185807102250b107a85001a00a1281d64002940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 952859091 1250 952857841 952857863
    0xe150f0a0807030f140705070309032012070303020703030804020102100c02011a0d08090123271206060103051807081c08070512040f06020705010f06050d170c0a 71
    0x200d0360204869200308000d0790b09121600c82c030f10300c02d8159110006445c04003c04140010501840745016107031841c001d24000118030b0b581e842c2c10003c0f88817212200c460b01c002e00381c04c102905084c241001c0c4a401c210042814030318540300252140402c0c00010b08011540020400350ba00c00c201481260542000800c200d400590029000700398040c1c518004040a901c3d00e01d9524010803039402194005014903d4040c0702401100c0c4010071181d80a15111241040d428040101c1c0c042e0190030225444012000070940c84a907404c03d4000c0ca5510400c812681022010004601c40740c009070282408582501c1300c01481300c6820944001030302500c9540300c0002d401e000050b00528401b01e03000500c07010400c005013280c4a240450b04200410401c1044030441c0b112140d05503032160088950424942103940c9070000ea0f8407020094070075a44603183c0d030304085680d11408000340011078074141c043c00d050395000b00a6202124440440e00d011594a114680030b21199400903400380700c40c0c072 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 952860341 1250 952859091 952859107
    0xc02030f0604110105040f0e0912070506150a0305030d0903050409410426120a0b0301180b09070e0c03091b0105040e072a03110d0e150f 60
    0x565039000700c400f640c02000c00c26002c0c80a5019004030380680c1c0790542c500c00b0b85400e1503001c00b40184e000c0c103040d94511074007003c40722090039080900790440c450f1000d054942032114071034003140e003600c06261046440d41c5c8100b000510000c21610700554036040481c490809040507109400f60341d00c0161110f04282c800d1003600c07644211200c04c900c40500090000c8021042e040321040158882c41c210000c440105000c210f0000f681c0d110041c0300703900544071000720a003800742d540008030500340304200e5000307106c0e036407007203010302c403080314041e8020005403400c400f034110b81d40c4c03041f900600000b0480c40841d881150a11660000e0105585403140a043c90051600e550340100c51000f801c0c040c400d43c01595003180340c450003140a0580d40d076420301d8180191603132800c10183c0074000380441000b01c0103c0e05511014001e18181441c10400040c07002e040281c44494802d8007031880781c011046913084990003040c00b884100013554000d1001c88404130302d008130722911b00c14038580030010500d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 952861591 1250 952860341 952860343
    0x6181202040e06011d0c0306030c0d050a060c0306050315060a180b09070203090901091401030b0c0c07090f0608071a1b0609162408071202180a0e090705010c030c02030f 74
    0x1000090b16041e020b0040e0b503e901c50520b0602088e01c50542c19048850011460724195003500700c0c050180054818030b4456541d4034080752140c0104c000465103a8008108501c1c1c00e0004c1c070300004185442002c01d151042c00140d007480103004030454000408140206a001a813240039a800050305c03000c4a42000702c40695650000c1609074071940000c0e00100b55143c482c0144580c0d100e081d000c0a6403642156540d40301480000c1906040c0c0000703105100c0ca0090410010f03004000748640007540c9802c511010303040e102141c1005040d40c4c00f00100700402400790b140510295180326516448142c042944030030500a640b01c0c046521450080c41185c40000c074441009007450400f007145180d4492880300c4155102a0b02405101480c00c1c2001d820301402c0e089a02c4180c03880d025a01e80849a41c0344204d80241d5800d000040803c8021022401c2c055001d0000d484400e401803c1840c00401241c1d803007541c0e0107014104000c0c04104401c043c0600172459110790700800340c0300604500d4611b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 952862841 1250 952861591 952861619
    0xf0706030e0c030601032a1206020313020301140703200910090f0311270a1512050715020a020a0b07021908010c09060f02150c0d0c081006181202040e0601 68
    0x10042031032001f042919104030031201904644800200d40c103c01e0154036110001d400040000c1d8603500d480000c4401131b0380c213200f0b040003a00d040e86d10000070300302048010229500088002503c901408c2c0e1090f511241e00c1c1510445101181d824084980c100021a4441c80c55072001c411443c00420102c108440710320107001c01c20041d07500c0214840114501d013448417810303030450340c40c2144101140500c402c0d6008039a21480045440d84071175038490080101078036410301510560041c0e2000e004500c8524031400b401c01c0c00e48028508480c2a80000c1c01021040c4622a912600080c40c0d8046490391000135000b0b50405081325139469079012207030b0207442094003820010b40c68800c0420910b0165170111b504507a01c1e4020708142015080d40d52107150064100c0703506060620200d0700409807805210305580c86662516142c0c1415014982074400316040602484440d454004404900f10a01d8045130000414080075802e07600204e401000c0112500c9564001c503000031841c24100b40310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 952864091 1250 952862841 952862873
    0x3060612091f0c0e0f12060a090308160215040302120a1d041a0d020a15030e060708010b1c1503140d080f181c030501050108090f0706030e0c03060103 66
    0x6965200341c2c2000c842e040b20003194101c00407851155003c10300e4181034070b009031908400790510204810821a09151450441d0041583c5840e2030448040641c000c0c1d003241c10040d02c080c03420f030302603044e10701944558058455001e0144000c0c000f906162080046c2c24074400070110303651f911401c82000030060480701c040c000c42c000c40c0740c480022600b00b0740315030748820f046003041c0031010781e101041115828008005a03030201090320007183c030303400c01e0404a40007200b54174001000340c106000345041540040c503070414000900010441c560356881140c3d010310640080a03201844034103004000c10040b001e8a000c00310a66000c0100281c684000c8040621b40d001c6079a040b008000446401500b103882003010031071170011a8520110212540c9480302000035529038581e400c0f080d00305035000d9070b100d000080c0c032240100107958000a01640000d0a60050030800d00c0d010550344d5504083c1c4913442c10181c0e94802c0b42c02210301400a03092401000302a24080d507964205501d0100c07022203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 952865341 1250 952864091 952864123
    0x702040b031c0e1e0d06181505100501080906040210031119080907050a0b031005060f0a0f0c031e051b07051f1b0c030807150b030606150306061209 65
    0x542c80708000320b1110500380d0384c20092561100342d035641d860801030004420981d08542c02d004a8070001900c450030038000140b81500041c0900d090360403598400c0329540250306100c050360038048503000204080360f102e5010345056406044001040740102800c010f1510800c102003425408003d08600c0481980d0a03981c9418050710340ca80e5003a194012031041e142d004458030380c10800a00101c1c09141e02001303440644581960f10000b0401d1680301c480e00011884001a174107400f0740d0880d0185d1b040318120314025501e2080c554010300141c004290501c080c1459844940b1400e00c00c100311000440d40e02281c0c0801c42100b4000340d504da41038061140705606d0f03101c03100800c80303841c406c04200d403400d95113010200f46a0307524200c4920b100007041d10b04880002c40440862003c00007044060703c10441c41c150f1507004007454003100e00700c2d22a01e1082c1c102c00213000040da12041c01070b4030340400c4150140d80703803079003c00209107105900c6a00e5099a1280c10000f1004001c40d2051141007811 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 952866591 1250 952865341 952865359
    0x9030c180702010b09010f050409061103090a0512030708010e15061309140609040b0702030702030312010603230604110d05010e0601120207030807120f05390702040b031c0e 76
    0x1304006900324240548580700410080030885031400360040250030303014000c00a880e07006826400c1c81790380125640c8500b50702c4560301c2c50421800b04000280d01d03441008113400c0d42031860b00103104041c10300ca103132207070000742c004100d0410000c0282511752000821065840e03103160142008480070788154040a807a24440c1841a6020a0100e101d0400201040300039940d598800061160161441f000c40c882804a100161410001843d14101040161202d0361401d580141a20394000d0603102d00080c484102c000d041d1001c000c16040702d4200c4012620790840b104c62016400745810440d501d0341040000075901f4600119680100400e03602c0848011140100d0b2040e03119004004000803511800540014800c203203022540401c0748000c10341e06502c10311801030303c50950301c0050010f2a8801d44014480803107070030444502045c01200b400ca0400401c00c4180291200a4059915941481810756052088005000c4104500412000c0c0d00d440100003441080000b401101c0b01d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 952867841 1250 952866591 952866611
    0xc090606020a0503070201030e120c0102030115030e0a03030c02120d020703090b12130c030515010929040b0105041502010b15250303110a0e100e090c09030c18070201 73
    0x2240d44410107400000845c0342241d181c3c01100100348402e003010b40f40c000c880458450851b030f403000304840c0280d28005070300c0354181001c2009601c05010341c51700381480d0641e08140d158003c5810a21182c1600b00051008607811040e410088046013294400343c00007503000c000f141c15400303009030501a946021030151682542441e510072b450004082c001590700040c0e07419040100000c0703030780c0318925000307682da42d0b03659039890003400c0c141c1c4010080d103900c0180b00c0030b22180304114007081e00c1e4209058042c0d480c1070b02c036029914000c01e00d0080383c41c2c101458223a4003c04c01c440c001c0885c080035a42203019000000d0080180038161846200c1081240107821510825284c0c8020140e0a1904015460026210348200701c0f03003c4003856260840d03110154800c00150000205d140c5aa0340000405000c000d104c40044040905000f4000381140c15500d41d01d0030907070701c10704071915650f81d0f0443c5070000c4d00d01752011030703956807100950f90100078100700b60034803500508181c0c0003888842e4075 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 952869091 1250 952867841 952867843
    0x6070f0c060507020d0b0a1404030302030906220602090a17030c010c1d1e0901090b0127050105130f062a052802032b0203040f090f0e0a0c09060602 65
    0x1032080c0131798042070717150070032000c1094150110b40240c01d20000003114144400003141c0b14000b1201900403d50100400810040500c0320303e03070080640700c00b1400304411000081c0d01148190010b41082e81c045007001654440002e0309c000340c4001740138500d00503010816a40c1c4e0703038007400d12100c142d401c042010b5030310340c000d1000c01c511502842000b101d482910302800117002c80da80e802840702503642e2080302c0c0c60702c42600c1c00e40601500c0001081c082c05130706c000344c10080700031126501090780584441c4001907881c1d520003954001d1070034030b40d02c18145149224010485d00400360040c01d10400181242e0040c4000ad424041c200c0200c40340c2207050a0300e101c1c1082c0c003402030102d8010310f80440a0840440c000d800d50b442107002007418606a8000c0781c50300c42e1403043c0c910a800f000d454007940107000781c0031184501e1148021842c0500341000c119010b007480c8034900c1700645810f44801440644e0b004030b40502d05c64400c0719040703116420b1802c1034081c1031084e00c030101d03e03018020840603c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 952870341 1250 952869091 952869097
    0x9021801080d020f1b040203060105070c1403150907050111105a090b09030c010b060301030f0321150f38040812070b0708090a170906070f0c0605 64
    0x40300c441c4810405e039841070002030360005003580e040160400c0001c0001e07601c2154803010300307070000e1a28181160101410315184281e02c81c48010520f0f401006035101001484805648080c6000030fa200c0c0554116440e1000d113014111701c0e2030400329101010403000014030300381e0200c8043c0c03104090341c0d8450009040c9420341c0e09840410415606c50f50380849515044010a0000000502204549840c407200c3d1003a108000e094100003941c982d40e8000f405080c0d8440400c031a400e2846d455641c51007201081964001c00703000e050150061000b650162950054110710000e000f49000380e0740d070f482408600c5c001c005403040340d64008580614540150740180c1c5040409482e00b2503627400c6450307440806c804000440d8820000130499000501c02d690704460051000c0da222100384c682a4440000141040c1c10000d410301000b4801034002034071000903401805900c03500488400e21501032040c107000e80d8101000082138801c00c0131b40c16108540e03a01503802c507050140c40f58800c548070301c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 952871591 1250 952870341 952870363
    0x21806010917030316020c030d18050406050315060d1e02120f03040b07060b220b0405060a0905040c090c0f0809010e0601030314120709090e0105010503030d09021801080d020f 77
    0x2600c18800640d8034414102e40034413030000c0d40111f403c0c1d0800080007a19004c1405101d82c000b4848a200c840d0000704040354401401085405004142c20100400c0e903421507503c0040000c003054022401a490780e0f04040c03101504070900722945080d01500c0003a0800d100c60480c05810318a0392000c906c440414208069040500914602498400c1c0c4040e5500302c5601070369102c1d500c4d10906403540c3e6045d40001d1942d0801919010039074061002001c944801e00c00341d000c1e50034081040700c60b030b07a2480840c0644081000000707094403103091682c00c0309010341040514074913010642c4c01e10751b0801c80480c1640720780e68612805980310200346d42610345480e03142c0341c00d5000400500c0080c2c010b040b214041d01c070314a0640d0070a9107002640055000035103403640442c03980c10092000000318003e000040316100001d00440d454000840d64900c648069000b005984202c40411990fa0940082c1c41c03034580e12092900d941c482c550a030311009004180c2c0054841c0036283c1000c010f0100c2c00c1c0041f8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 952872841 1250 952871591 952871593
    0x516080301060e0f030d030e07150918090f032d0206090f01060e0c0a0507060203070905040b0609150c0307050a0b0a180c06120b040c110f0a0816030c021806010917 72
    0x445580f0790107801a1101640e0003d650127848800308044054504401882d4000e9444034100c51a00629810360310003052015061400d140d045800705c0c00c0341d81c03c410b103e40d15190403282108854020b4645420b80709500440103024401004c1103940041d065010b049814140d80038000321801941c00c03606907215544035070600000140c3c920061901400448116007071561624440c0c0d59182c040740d008843c000c01040344501700307011038141482090101e0200b51001443c0c4041c208c00109c14032110b41c4507080d54440040e43c0040d0741814000c0e101ea1652010890ba1288440e1400705124071003158900103562410201c110b0104807900170307102c81900a5140360490741404030481d9005400c0207082082511512140aa600c1c0d61141c0106035400d03589100881f11a03505142c241100b00d03050700740ca0f600425040010550507400c079114101c007400c0c5204125024503080e16600786c407003000b0350b0010554400c400e0030300380d0640151051030700366110000f46440e01202c0c8041c5001d40c40e02006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 952874091 1250 952872841 952872853
    0x109050c040c050426031c050415020f0909060102030c1f14011208090f100c0201110d020d0e0f300d050d1802060f040e0a05040519030516080301060e0f03 68
    0x40070303c540022040c4005040c00d8a00d082c040140845010050301f4240351050f07610b6040006008a0740030390800740080b080c0662810340c0c0381d80c8058180c0195825144110705402c0801c4023a03008004980051118900703542c1d0107a56030110200f0100a0401011424181b440baa040c0141c0115041c3c1a10741224025141c1195900e5505545e003060550340d40142d221001d6600c20390712050450543c0e00d55556042e4040e04a100052a000c0e800c41c400c1082d40c40f109003403002c1600454000f1f05540e103490040403040704c0c400001c29513004502c00c0c90b003220f4005143d03000004601501003a00c4500c501f217045000040d48a0355070b49a4980001c1d0001d20280092082d00c042c613009100c402c5200c889005803640030350000f5110358052440340440e080f00150803c0380038845c1c140b00794402d6200c40200071902d016128561520369420340e0050a084c0b4603030303040030180280300782e40341898484104014051145031a182030362081c01030801003180d03200310808900c1c2072401038003501c9002d0302400b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 952875341 1250 952874091 952874129
    0x121e050c040e0f0705041211040c03090b18070b2227090203030d061e090501051c03091e0e2220040207050313080313031509050109050c040c0504 64
    0xe0010082c0c901c00802004010002d040b40103c960b10072a240121070140c10a0030f2300c41000210390643e04d00e9801e041c1044c2807480485c01c60700b805948032036001c1200200d802d600c0020350030030303056400469810300301148225451000c9010090030145070215018020340f00c0840200c0300c7e24400340c03080902c407840c0ea07400c0122025003041030242d00c00390441c1c1c2800a8010b0480c140c43c0250441c201c81e007030000000340944c201a224a00070a00e00508208950400000c0707001403035100c02c81008405503040b4042054400d4120394004c2c0001daa018081144201500c481c0030070358030030b6050000c2d0b854040b504010f0314612000311a0103101d076601c0c84003025038807070000d4041d0030110400c002c041500650641c4990004007000b91140303001d1966004903105005180c41f80390801c41c49170b4402d00011010660070680030041e25044280060310407000010701d4050720b00341d50014855402e08080310100000092481800340044405000d1201d0380102200c00d4003681c4990300b42c0c134180ea4406e61f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 952876591 1250 952875341 952875361
    0x70e040201090839041407080604020a020318030a170c0d0e01020a0311070810060e070c0314031b0403030c0b16090e0901020904110301061d010519121e050c040e 71
    0x381c5130911508449041a0301c5500003412118000c50714211303a04408104943c66034441e040d1680058120b038110f0400c911100001c1d540d0141d06c40c1419144802d48116606603400c000881000e83c0c0007140305002c1e1507003030b5682d0094000211946103803003140c150300c5109010b10000741e030341c08060340186910300664804036a580001e03640499180071308580441d000b0000d1058242c03032141000e010034042c0c070340703028800d04c508001c11050400c0001d01106e000260310522004012200390b0307601e6165103a00000c81741e90001c0d80e4440c1101100024000200354004102c109103038010001711041e5640c01c1d20381d0011241c00446c00c0001040400140f140c02d00c0304095580241c240400141031620305e0b8003150458100a400645c103034408001002500d5024074144404a101f001c0c1101c1c3e00080d02c006081c9016481c840c3d0740704514807025100b1075209248481c8801e12183c02070050842050300c0030348d22420040004001070429000801f11b84010701228100e88089054000c5c0d079890203d50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 952877697 1106 952876591 952876663
    0x20102070902090d081e0a031a030111030604090c0806010b040e012310020c10051b0319050a1808010b0f0f0a140d0203070e0402010908 60
    0x3c0015440c0d6011107902144c2c4075001c2500c684610051080b000551241001c0c3d10101217114032a403035054111a44c0c40d001640308654040c8001e09043c03c0c0c40301d00301f0815101d50208046010385c101680561007860244203940900798840c0300701030804000ba404540c03459000304041c0040715003e56124010702051915807881c041e2810661500c4201d412001d1043c400780b8404521a802030110300c1c41c68000070240402c03103c0501010f0700b1600102c400c00700510740910241a404000022602d1a01d80f40d0721405896581c2c0204803032903800a008c40c1d0411100a0b6401680e0707285901031390181500100124001c49400c05010f11580740074500d40c40780585521084c51501e4034400328050725a41c1c0d0007a05058240004107110700c82d07040000703402d8400c1b40400030700035110303440c2a80128400d0740c075070310400c1e0b5483d0110380c0c1d10328056844030341c1545901404090308043c480 = true := by decide +kernel

theorem cover : BRFrame.Cov 952697841 952877697 := by
  have h0 := BRFrame.cov_init 952697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 952697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 952697841 ≤ n) (h2 : n < 952877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
