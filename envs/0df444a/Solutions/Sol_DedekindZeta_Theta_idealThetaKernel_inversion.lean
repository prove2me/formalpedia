-- Prove2me | solution 1 for DedekindZeta.Theta.idealThetaKernel_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:35:04.706014+00:00
-- url     : https://prove2.me/submissions/f30cf389-7d23-4699-9d51-f12db38736b7

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_idealThetaKernel_eq_mixed
import Theorems.Thm_DedekindZeta_Theta_mixedThetaKernel_inversion

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0)
    (x : mixedEmbedding.mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    idealThetaKernel K 𝔞 x⁻¹ =
      ((|mixedEmbedding.norm x| / covolume K 𝔞 : ℝ) : ℂ) *
        (mixedThetaKernel K (dualIdeal K 𝔞) x + 1) - 1 := by
  rw [idealThetaKernel_eq_mixed]
  exact mixedThetaKernel_inversion K 𝔞 hne x hx
end DedekindZeta.Theta
