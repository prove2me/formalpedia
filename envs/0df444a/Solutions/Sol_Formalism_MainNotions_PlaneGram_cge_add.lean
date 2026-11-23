-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:52:28.652564+00:00
-- url     : https://prove2.me/submissions/d4205a53-919c-426d-8d9c-ef5866e0cade

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_add

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
theorem _root_.solution {σ : Type} {a : ℝ} {F G : MvPolynomial σ K} (hF : cge v a F) (hG : cge v a G) :
    cge v a (F + G) := by
  intro α
  rw [MvPolynomial.coeff_add]
  exact vge_add v (hF α) (hG α)
end Formalism.MainNotions.PlaneGram
