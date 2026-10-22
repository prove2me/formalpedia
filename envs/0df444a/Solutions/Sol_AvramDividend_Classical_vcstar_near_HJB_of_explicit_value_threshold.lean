-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_explicit_value_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T10:56:13.721823+00:00
-- url     : https://prove2.me/submissions/bfea371e-e34d-4ed9-bf8a-39b9cc7e1040

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_unit_value_regular_minimum
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
The affine branch converts the reserve threshold into the two hypotheses
required by the full nonlocal, unit-value near-field HJB theorem.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (hbarrier : 0 < (cstar W).toReal)
    (hminimal : ∀ z : ℝ, 0 < z →
      deriv W (cstar W).toReal ≤ deriv W z)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hthreshold : (cstar W).toReal +
      max 0 (max (X.c / q) (1 - vcstar W (cstar W).toReal)) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  let a : ℝ := (cstar W).toReal
  let m : ℝ := max 0 (max (X.c / q) (1 - vcstar W a))
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hvalx : vcstar W x = x - a + vcstar W a := by
    have hx0 : ¬ x < 0 := not_lt.mpr (le_trans ha (le_of_lt hx))
    have hxa : ¬ x ≤ a := not_le.mpr hx
    have ha0 : ¬ a < 0 := not_lt.mpr ha
    change barrierValue W a x = x - a + barrierValue W a a
    simp only [barrierValue, if_neg hx0, if_neg hxa,
      if_neg ha0, if_pos le_rfl]
  have hm0 : 0 ≤ m := le_max_left _ _
  have hmdrift : X.c / q ≤ m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hmvalue : 1 - vcstar W a ≤ m :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hthreshold' : a + max 0 (X.c / q) ≤ x := by
    have hmax : max 0 (X.c / q) ≤ m := max_le hm0 hmdrift
    change a + m ≤ x at hthreshold
    linarith
  have hunit : 1 ≤ vcstar W x := by
    change a + m ≤ x at hthreshold
    rw [hvalx]
    linarith
  exact vcstar_near_HJB_of_unit_value_regular_minimum
    X q hq W hW hreg hpositive hbarrier hminimal x hx hunit hthreshold'
