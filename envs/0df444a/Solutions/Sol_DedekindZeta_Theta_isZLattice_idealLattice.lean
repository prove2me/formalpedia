-- Prove2me | solution 1 for DedekindZeta.Theta.isZLattice_idealLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:16:33.036752+00:00
-- url     : https://prove2.me/submissions/af1a5c43-b7a9-4f97-a4e8-92ed98816afb

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_idealLattice_eq_comap

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    [DiscreteTopology (idealLattice K I)] :
    IsZLattice ℝ (idealLattice K I) where
  span_top := by
    rw [idealLattice_eq_comap K I hI]
    exact (inferInstance : IsZLattice ℝ (ZLattice.comap ℝ
      (mixedEmbedding.idealLattice K (Units.mk0 I hI))
      (eEmbℝ K).symm.toLinearMap)).span_top
end DedekindZeta.Theta
