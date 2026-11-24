-- Prove2me | solution 1 for Formalism.HN.duality_linIndep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:25.537656+00:00
-- url     : https://prove2.me/submissions/9b80901e-1f35-4def-9d49-49fda54a1037

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_inner_sum_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.HN
theorem _root_.solution (v w : ι → E)
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) : LinearIndependent ℝ w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  rw [← duality_inner_sum_dual v w hvw g k, hg, inner_zero_right]
end Formalism.HN
