-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.lin_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:28.726113+00:00
-- url     : https://prove2.me/submissions/301e3e49-ec0a-4934-9f37-674d4ec02e61

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ τ : Type} (T : MvPolynomial σ K →ₗ[K] MvPolynomial τ K) (Z : MvPolynomial σ K) :
    T Z = ∑ ζ ∈ Z.support, Z.coeff ζ • T (monomial ζ 1) := by
  conv_lhs => rw [Z.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [show monomial ζ (Z.coeff ζ) = Z.coeff ζ • monomial ζ (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
end Formalism.MainNotions.PlaneGram
