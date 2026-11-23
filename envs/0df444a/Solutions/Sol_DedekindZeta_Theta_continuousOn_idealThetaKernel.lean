-- Prove2me | solution 1 for DedekindZeta.Theta.continuousOn_idealThetaKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:18:11.175938+00:00
-- url     : https://prove2.me/submissions/4d867b6c-c9dd-400b-9fd9-09bd154f89b8

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
import Theorems.Thm_DedekindZeta_Theta_continuousOn_mixedThetaKernel

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) :
    ContinuousOn (idealThetaKernel K 𝔞)
      {x : mixedEmbedding.mixedSpace K | mixedEmbedding.norm x ≠ 0} := by
  have h : idealThetaKernel K 𝔞
      = mixedThetaKernel K (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
    funext (idealThetaKernel_eq_mixed K 𝔞)
  rw [h]
  exact continuousOn_mixedThetaKernel K _
end DedekindZeta.Theta
