-- Prove2me | solution 1 for Formalism.HN.duality_inner_sum_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:18.670468+00:00
-- url     : https://prove2.me/submissions/13bbefa9-ee8e-4837-b72e-1376a1785bf3

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality

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
    (hvw : ∀ k i, inner ℝ (v k) (w i) = if k = i then 1 else 0) (c : ι → ℝ) (k : ι) :
    inner ℝ (v k) (∑ i, c i • w i) = c k := by
  simp [inner_sum, real_inner_smul_right, hvw]
end Formalism.HN
