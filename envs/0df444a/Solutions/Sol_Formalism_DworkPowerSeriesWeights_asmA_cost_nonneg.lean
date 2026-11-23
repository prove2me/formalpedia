-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_cost_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:00.921799+00:00
-- url     : https://prove2.me/submissions/1576c281-bd37-4070-97a1-be013a447a5e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) {d : ℕ} (eps : ZMod d → ℝ) (p : Option (ZMod d × ℤ)) :
    0 ≤ asmA_cost l eps p := by
  rcases p with _ | ⟨s, j⟩
  · simp [asmA_cost]
  · simp only [asmA_cost]
    split_ifs
    · exact le_max_right _ _
    · positivity
end Formalism.DworkPowerSeriesWeights
