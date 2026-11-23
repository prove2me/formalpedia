-- Prove2me | solution 1 for DedekindZeta.Theta.idealLattice_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:11:30.928157+00:00
-- url     : https://prove2.me/submissions/cd1b0a6c-02f0-4684-b1db-0a83de9fc8b5

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    idealLattice K I =
      ZLattice.comap ℝ (mixedEmbedding.idealLattice K (Units.mk0 I hI))
        (eEmbℝ K).symm.toLinearMap := by
  ext v
  rw [mem_idealLattice_iff]
  rw [show ZLattice.comap ℝ (mixedEmbedding.idealLattice K (Units.mk0 I hI))
        (eEmbℝ K).symm.toLinearMap
      = (mixedEmbedding.idealLattice K (Units.mk0 I hI)).comap
          ((eEmbℝ K).symm.toLinearMap.restrictScalars ℤ) from rfl,
    Submodule.mem_comap]
  rw [mixedEmbedding.mem_idealLattice]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [LinearMap.restrictScalars_apply, ← eEmbℝ_mixedEmbedding]
    exact (ContinuousLinearEquiv.symm_apply_apply (eEmbℝ K) _).symm
  · rintro ⟨a, ha, hav⟩
    refine ⟨a, ha, ?_⟩
    have : eEmbℝ K (mixedEmbedding K a) = eEmbℝ K ((eEmbℝ K).symm v) := by
      rw [hav]; rfl
    rwa [eEmbℝ_mixedEmbedding, ContinuousLinearEquiv.apply_symm_apply] at this
end DedekindZeta.Theta
