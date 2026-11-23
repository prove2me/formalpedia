-- Prove2me | solution 1 for DedekindZeta.Theta.map_toMinkowski_symm_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:22:03.09623+00:00
-- url     : https://prove2.me/submissions/f670a814-e636-402b-8cde-d7f784ba846f

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_det_scaleMixed_symm

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open MeasureTheory
namespace DedekindZeta.Theta
theorem _root_.solution :
    Measure.map (toMinkowski K).symm (volume : Measure (minkowskiSpace K))
      = ENNReal.ofReal ((2 : ℝ) ^ nrComplexPlaces K) • (volume : Measure (mixedSpace K)) := by
  have hsq : ((Real.sqrt 2)⁻¹) ^ (2 * nrComplexPlaces K) ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    positivity
  -- `(toMinkowski K).symm = (scaleMixed K).symm ∘ toMixed K` as a function.
  have hcomp : ((toMinkowski K).symm : minkowskiSpace K → mixedSpace K)
      = (scaleMixed K).symm ∘ (mixedEmbedding.euclidean.toMixed K) := by
    funext w
    show (toMinkowski K).symm w = (scaleMixed K).symm (mixedEmbedding.euclidean.toMixed K w)
    have hw : toMinkowski K ((scaleMixed K).symm (mixedEmbedding.euclidean.toMixed K w)) = w := by
      rw [toMinkowski, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
    exact (ContinuousLinearEquiv.symm_apply_eq (toMinkowski K)).mpr hw.symm
  rw [hcomp, ← Measure.map_map ((scaleMixed K).symm.continuous.measurable)
    ((mixedEmbedding.euclidean.toMixed K).continuous.measurable),
    (mixedEmbedding.euclidean.volumePreserving_toMixed K).map_eq]
  -- Now reduce `Measure.map (scaleMixed K).symm volume` to the linear-map formula.
  have hcoe : ((scaleMixed K).symm : mixedSpace K → mixedSpace K)
      = ⇑((scaleMixed K).symm.toLinearEquiv.toLinearMap :
          mixedSpace K →ₗ[ℝ] mixedSpace K) := rfl
  rw [hcoe, Measure.map_linearMap_addHaar_eq_smul_addHaar volume
      (by rw [det_scaleMixed_symm]; exact hsq), det_scaleMixed_symm]
  congr 1
  rw [abs_of_pos (by positivity)]
  congr 1
  rw [inv_pow, inv_inv, pow_mul, Real.sq_sqrt (by norm_num)]
end DedekindZeta.Theta
