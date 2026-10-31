-- Prove2me | solution 9 for AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:59:31.546953+00:00
-- url     : https://prove2.me/submissions/acdecbbc-ef4b-47e6-ab1d-58ab6bb5f5a8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_excursion_integrated_scale_representation
import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_continuous_excursion_log_derivative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Direct C1 regularity from the genuine continuous excursion-tail integral
    representation, with no auxiliary differentiability assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    rcases hbv with ⟨_, hfinite⟩
    rw [hvar] at hfinite
    exact (lt_irrefl (⊤ : ENNReal)) hfinite
  obtain ⟨φ, μ, hφ, hnull, hfinite, hcont, hrepr⟩ :=
    unbounded_esscher_excursion_integrated_scale_representation
      X q hq W hW hnbv
  have hderiv : ∀ x : ℝ, x ∈ Ioi (0 : ℝ) →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x := by
    intro x hx
    exact excursion_integral_scale_derivative
      W φ μ hcont hrepr x (Set.mem_Ioi.mp hx)
  apply contDiffOn_one_of_continuous_excursion_log_derivative
    W (fun t : ℝ => μ.real (Ici t)) φ
  · intro x hx
    exact (hderiv x hx).differentiableAt
  · exact hcont
  · intro x hx
    exact (hderiv x hx).deriv
