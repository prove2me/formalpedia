-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exists_bound_mixedThetaKernel_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:45:07.074793+00:00
-- url     : https://prove2.me/submissions/8233e347-2b06-4c0d-8d76-6c9f59bd77e4

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_isCompact_closure_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_mixedThetaKernel_radialMap

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K)
    (r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, ∀ σ ∈ normEqOneSurface K,
      ‖Theta.mixedThetaKernel K I (radialMap K r σ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closure_normEqOneSurface (K := K)).exists_bound_of_continuousOn
    (continuousOn_mixedThetaKernel_radialMap K I r hr)
  exact ⟨C, fun σ hσ => hC σ (subset_closure hσ)⟩
end DedekindZeta.ConeRadialReduction
