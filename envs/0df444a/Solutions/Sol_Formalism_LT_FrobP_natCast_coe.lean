-- Prove2me | solution 1 for Formalism.LT.FrobP.natCast_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:54.592629+00:00
-- url     : https://prove2.me/submissions/a1d6e86d-02d0-453b-8850-a4896415e168

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.FrobP
theorem _root_.solution (p : ℕ) : (((p : unitBall K)) : K) = (p : K) := by
  first
    | exact map_natCast (unitBall K).subtype p
    | simp
end Formalism.LT.FrobP
