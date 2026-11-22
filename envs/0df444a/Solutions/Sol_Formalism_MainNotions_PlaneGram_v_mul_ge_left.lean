-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.v_mul_ge_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:25.234167+00:00
-- url     : https://prove2.me/submissions/5fa42baf-cd5e-4d86-8a4c-56fd6f9fd382

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {x y : K} {c : WithTop ℚ} (hx : c ≤ v x) (hy : 0 ≤ v y) : c ≤ v (x * y) := by
  rw [AddValuation.map_mul]
  exact le_add_of_le_of_nonneg hx hy
end Formalism.MainNotions.PlaneGram
