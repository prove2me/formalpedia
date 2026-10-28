-- Prove2me | solution 4 for AvramDividend.Classical.cstar_finite_zero_or_deriv_minimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:48:59.515592+00:00
-- url     : https://prove2.me/submissions/e86a95d0-a621-468b-b6c4-46a3de039acd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary
import Theorems.Thm_AvramDividend_Classical_continuous_argmin_sInf_zero_or_minimal
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_eq_sInf_of_nonempty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive-axis C1 regularity closes the finite argmin-set infimum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ ∧
      ((cstar W).toReal = 0 ∨
        (0 < (cstar W).toReal ∧
          ∀ x : ℝ, 0 < x → deriv W (cstar W).toReal ≤ deriv W x)) := by
  obtain ⟨hpos, φ, hφ, htilt⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hC1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact hC1.differentiableOn_one.differentiableAt (isOpen_Ioi.mem_nhds hx)
  have hcont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl _)
  have hfin : cstar W < ⊤ :=
    cstar_finite_of_normalized_monotone
      W φ hφ (hpos 1 (by norm_num)) htilt hdiff hcont
  constructor
  · exact hfin
  · by_cases hS : (cstarSet W).Nonempty
    · have hArgmin :
          sInf (cstarSet W) = 0 ∨
            (0 < sInf (cstarSet W) ∧
              ∀ x : ℝ, 0 < x →
                deriv W (sInf (cstarSet W)) ≤ deriv W x) := by
            simpa only [cstarSet] using
              (continuous_argmin_sInf_zero_or_minimal (deriv W) hcont hS)
      rw [← cstar_toReal_eq_sInf_of_nonempty W hS] at hArgmin
      exact hArgmin
    · have hzero :=
        ((cstar_lt_top_iff_minimizer_or_zero_boundary W).mp hfin).resolve_left hS
      have hc : cstar W = 0 := by
        unfold cstar
        rw [if_neg hS, if_pos hzero]
      exact Or.inl (by simp [hc])
