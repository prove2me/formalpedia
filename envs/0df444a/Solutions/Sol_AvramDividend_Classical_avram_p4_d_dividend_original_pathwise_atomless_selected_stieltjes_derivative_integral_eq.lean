-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_pathwise_atomless_selected_stieltjes_derivative_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:57:07.029935+00:00
-- url     : https://prove2.me/submissions/56a24721-7ae5-4c70-8860-fd074dee0e62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ) (hA : MeasurableSet A) (hApos : A ⊆ Ioi (0 : ℝ))
    (q : ℝ) (w : ℝ → ℝ) :
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) =
    (∫ s in A, Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω)) ∂ν) := by
  have hstate : ∀ᵐ s ∂ν, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω :=
    avram_wave4_04b_all_source_pathwise_atomless_prejump_for_path_dependent_measure
      X x D hD ω ν
  have hstateA : ∀ᵐ s ∂ν.restrict A, 0 < s →
      riskProcess X x D s.toNNReal ω =
        x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω := ae_restrict_of_ae hstate
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hA, hstateA] with s hs hEq
  rw [hEq (hApos hs)]
