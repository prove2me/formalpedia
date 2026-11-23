-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:14.097489+00:00
-- url     : https://prove2.me/submissions/d6cbdf1c-2172-4f20-a7bf-73ef3fe6b2c2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul

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
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} {a b : ℝ} {c : K} {F : MvPolynomial σ K} (hc : vge v a c)
    (hF : cge v b F) : cge v (a + b) (c • F) := by
  intro α
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact vge_mul v hc (hF α)
end Formalism.MainNotions.PlaneGram
