-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.integrableOn_mixedThetaKernel_radialMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:47:29.592144+00:00
-- url     : https://prove2.me/submissions/a55fa24a-3c78-4571-af4a-cf0c14ef61d9

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measurableSet_normEqOneSurface
import Theorems.Thm_DedekindZeta_ConeRadialReduction_measure_normEqOneSurface_lt_top
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_mixedThetaKernel_radialMap
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_bound_mixedThetaKernel_radialMap

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution
    (I : FractionalIdeal (𝓞 K)⁰ K) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) (surfaceMeasure K) := by
  -- Finite restricted measure ⇒ constants are integrable on `S`.
  haveI : IsFiniteMeasure ((surfaceMeasure K).restrict (normEqOneSurface K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_normEqOneSurface_lt_top⟩
  -- Uniform bound `C` on the kernel over the surface slice.
  obtain ⟨C, hC⟩ := exists_bound_mixedThetaKernel_radialMap K I r hr
  -- The integrand is `AEStronglyMeasurable` (continuous on `S ⊆ closure S`).
  have hcont : ContinuousOn (fun σ => Theta.mixedThetaKernel K I (radialMap K r σ))
      (normEqOneSurface K) :=
    (continuousOn_mixedThetaKernel_radialMap K I r hr).mono subset_closure
  refine Integrable.mono' (g := fun _ => C)
    (integrable_const C)
    (hcont.aestronglyMeasurable measurableSet_normEqOneSurface) ?_
  exact (ae_restrict_iff' measurableSet_normEqOneSurface).mpr
    (Filter.Eventually.of_forall (fun σ hσ => hC σ hσ))
end DedekindZeta.ConeRadialReduction
