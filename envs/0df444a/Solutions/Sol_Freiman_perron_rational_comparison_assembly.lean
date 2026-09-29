-- Prove2me | solution 1 for Freiman.perron_rational_comparison_assembly
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T19:58:52.007951+00:00
-- url     : https://prove2.me/submissions/cf9a11da-5738-4176-a1ba-ff1bbf4a9306

import Definitions.Def_Freiman_perronArithmetic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp

open Freiman

private theorem finite_denominator_bound (b : ℕ → ℕ+) (K : ℕ) :
    ∃ R : ℕ, ∀ n : ℕ, n < K → continuantQ b n < R := by
  induction K with
  | zero => exact ⟨0, by omega⟩
  | succ K ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨max R (continuantQ b K + 1), ?_⟩
    intro n hn
    by_cases he : n = K
    · subst n
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    · exact lt_of_lt_of_le (hR n (by omega)) (le_max_left _ _)

private theorem positive_coprime_fraction_unique
    (p q a c : ℕ) (hq : 0 < q) (hc : 0 < c)
    (hpq : Nat.Coprime p q) (hac : Nat.Coprime a c)
    (he : (p : ℝ) / q = (a : ℝ) / c) : p = a ∧ q = c := by
  have heq : (p : ℚ) / q = (a : ℚ) / c := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_div, Rat.cast_natCast] using he
  have hr := Rat.div_int_inj (a := (p : ℤ)) (b := (q : ℤ))
    (c := (a : ℤ)) (d := (c : ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hc)
    (by simpa using hpq) (by simpa using hac) (by simpa using heq)
  exact ⟨by exact_mod_cast hr.1, by exact_mod_cast hr.2⟩

theorem solution (b : ℕ → ℕ+)
    (hirr : Irrational (cfValue b)) (h0 : 0 < cfValue b) (h1 : cfValue b < 1)
    (hnearest : ∀ q : ℕ, integerDistance ((q:ℝ)*cfValue b)=|(q:ℝ)*cfValue b-(nearestNumerator (cfValue b) q:ℝ)|)
    (hescape : ∀ R : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q≤q → R≤reducedApproximationDenominator (cfValue b) q)
    (hlegendre : ∀ p q : ℕ, 0<p → p<q → 2≤q → Nat.Coprime p q →
      |cfValue b-(p:ℝ)/q|<1/(2*(q:ℝ)^2) → ∃ n : ℕ, cfConvergent b n=(p:ℝ)/q)
    (hconv : ∀ n : ℕ, cfConvergent b n=(continuantP b n:ℝ)/continuantQ b n)
    (hcop : ∀ n : ℕ, Nat.Coprime (continuantP b n) (continuantQ b n))
    (herror : ∀ n : ℕ, 1/((continuantQ b n:ℝ)*|(continuantQ b n:ℝ)*cfValue b-(continuantP b n:ℝ)|)=perronValue b n) :
    ∀ K : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      approximationValue (cfValue b) (q + 1) ≤ 2 ∨
      ∃ n : ℕ, K ≤ n ∧ approximationValue (cfValue b) (q + 1) ≤ perronValue b n := by
  intro K
  obtain ⟨R, hR⟩ := finite_denominator_bound b K
  obtain ⟨Q, hQ⟩ := hescape (max 2 R)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / cfValue b) (1 / (1 - cfValue b)))
  refine ⟨max N Q, ?_⟩
  intro q hq
  by_cases hsmall : approximationValue (cfValue b) (q + 1) ≤ 2
  · exact Or.inl hsmall
  right
  let d : ℕ := q + 1
  let m : ℤ := nearestNumerator (cfValue b) d
  let r : ℚ := reducedApproximation (cfValue b) d
  let p : ℕ := r.num.natAbs
  let s : ℕ := r.den
  let e : ℝ := |cfValue b - (r : ℝ)|
  have hd : 0 < d := by dsimp [d]; omega
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdreal
  have hNq : N ≤ d := by dsimp [d]; omega
  have hQq : Q ≤ d := by dsimp [d]; omega
  have hlarge : max 2 R ≤ s := hQ d hQq
  have hs2 : 2 ≤ s := le_trans (le_max_left _ _) hlarge
  have hsR : R ≤ s := le_trans (le_max_right _ _) hlarge
  have hs : 0 < s := by omega
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hs
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hsreal
  have hdx : 1 < (d : ℝ) * cfValue b := by
    have ht : 1 / cfValue b < (d : ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hN) (by exact_mod_cast hNq)
    exact (div_lt_iff₀ h0).mp ht
  have hdx' : 1 < (d : ℝ) * (1 - cfValue b) := by
    have ht : 1 / (1 - cfValue b) < (d : ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) (by exact_mod_cast hNq)
    exact (div_lt_iff₀ (sub_pos.mpr h1)).mp ht
  have hmposR : (0 : ℝ) < m := by
    have ht := Int.lt_floor_add_one ((d : ℝ) * cfValue b + 1 / 2)
    change (d : ℝ) * cfValue b + 1 / 2 < (m : ℝ) + 1 at ht
    linarith
  have hmltR : (m : ℝ) < d := by
    have ht := Int.floor_le ((d : ℝ) * cfValue b + 1 / 2)
    change (m : ℝ) ≤ (d : ℝ) * cfValue b + 1 / 2 at ht
    nlinarith
  have hrdiv : (r : ℝ) = (m : ℝ) / d := by
    simp [r, reducedApproximation, m]
  have hrposR : (0 : ℝ) < r := by rw [hrdiv]; exact div_pos hmposR hdreal
  have hrltR : (r : ℝ) < 1 := by
    rw [hrdiv, div_lt_one hdreal]
    exact hmltR
  have hrpos : (0 : ℚ) < r := by exact_mod_cast hrposR
  have hnum : 0 < r.num := Rat.num_pos.mpr hrpos
  have hpcastZ : (p : ℤ) = r.num := Int.natAbs_of_nonneg (le_of_lt hnum)
  have hpcast : (p : ℝ) = (r.num : ℝ) := by exact_mod_cast hpcastZ
  have hrps : (r : ℝ) = (p : ℝ) / s := by
    rw [hpcast]
    exact Rat.cast_def r
  have hp : 0 < p := by
    have ht : (0 : ℤ) < p := by rw [hpcastZ]; exact hnum
    exact_mod_cast ht
  have hps : p < s := by
    have ht : (p : ℝ) < s := (div_lt_one hsreal).mp (hrps ▸ hrltR)
    exact_mod_cast ht
  have hpcop : Nat.Coprime p s := r.reduced
  have hsdiv : s ∣ d := by
    have ht := Rat.den_dvd m (d : ℤ)
    rw [Rat.divInt_eq_div] at ht
    norm_cast at ht
    simpa [Rat.divInt_eq_div, s, r, reducedApproximation, m] using ht
  have hsd : s ≤ d := Nat.le_of_dvd hd hsdiv
  have hsdR : (s : ℝ) ≤ d := by exact_mod_cast hsd
  have hep : 0 < e := abs_pos.mpr (sub_ne_zero.mpr (hirr.ne_rat r))
  have heorig : |(d : ℝ) * cfValue b - (m : ℝ)| = (d : ℝ) * e := by
    calc
      |(d : ℝ) * cfValue b - (m : ℝ)| = |(d : ℝ) * (cfValue b - (r : ℝ))| := by
        congr 1
        rw [hrdiv]
        field_simp
      _ = (d : ℝ) * e := by rw [abs_mul, abs_of_pos hdreal]
  have hA : approximationValue (cfValue b) (q + 1) = 1 / ((d : ℝ)^2 * e) := by
    change 1 / ((d : ℝ) * integerDistance ((d : ℝ) * cfValue b)) = _
    rw [hnearest, heorig]
    congr 1
    ring
  have hgood : 2 < 1 / ((d : ℝ)^2 * e) := by rw [← hA]; exact lt_of_not_ge hsmall
  have hsquare : (s : ℝ)^2 ≤ (d : ℝ)^2 := by nlinarith
  have hprod : 0 < (d : ℝ)^2 * e := mul_pos (sq_pos_of_pos hdreal) hep
  have hsmallerr : e < 1 / (2 * (s : ℝ)^2) := by
    have ht : 2 * ((d : ℝ)^2 * e) < 1 := (lt_div_iff₀ hprod).mp hgood
    apply (lt_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hsreal))).mpr
    have hscale := mul_le_mul_of_nonneg_right hsquare (le_of_lt hep)
    nlinarith
  obtain ⟨n, hn⟩ := hlegendre p s hp hps hs2 hpcop (by simpa [← hrps] using hsmallerr)
  have hcq : 0 < continuantQ b n := by
    by_contra hz
    have heq : continuantQ b n = 0 := by omega
    rw [hconv, heq, Nat.cast_zero, div_zero] at hn
    have hpos : (0 : ℝ) < (p : ℝ) / s := div_pos (by exact_mod_cast hp) hsreal
    linarith
  have hmatch : continuantP b n = p ∧ continuantQ b n = s :=
    positive_coprime_fraction_unique _ _ _ _ hcq hs (hcop n) hpcop ((hconv n).symm.trans hn)
  refine ⟨n, ?_, ?_⟩
  · by_contra hnK
    have ht := hR n (by omega)
    rw [hmatch.2] at ht
    omega
  · have hereduced : |(s : ℝ) * cfValue b - (p : ℝ)| = (s : ℝ) * e := by
      calc
        |(s : ℝ) * cfValue b - (p : ℝ)| = |(s : ℝ) * (cfValue b - (r : ℝ))| := by
          congr 1
          rw [hrps]
          field_simp
        _ = (s : ℝ) * e := by rw [abs_mul, abs_of_pos hsreal]
    rw [← herror n, hmatch.1, hmatch.2, hereduced, hA]
    have hscaled := mul_le_mul_of_nonneg_right hsquare (le_of_lt hep)
    have ht : 0 < (s : ℝ)^2 * e := mul_pos (sq_pos_of_pos hsreal) hep
    simpa only [pow_two, mul_assoc] using one_div_le_one_div_of_le ht hscaled
