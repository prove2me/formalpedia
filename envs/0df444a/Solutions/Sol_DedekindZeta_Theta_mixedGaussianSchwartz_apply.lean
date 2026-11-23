-- Prove2me | solution 1 for DedekindZeta.Theta.mixedGaussianSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:18:23.889798+00:00
-- url     : https://prove2.me/submissions/1a3388a0-fa9d-4ee1-9607-13b68f2ffc84

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_mixedGaussian_eq
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) (v : minkowskiSpace K) :
    mixedGaussianSchwartz K hx v
      = (mixedGaussian K (x * (toMinkowski K).symm v) : ℂ) := by
  simp only [mixedGaussianSchwartz,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    gaussVSchwartz_apply, A_x_apply]
  exact (mixedGaussian_eq K _).symm
end DedekindZeta.Theta
