-- Prove2me | solution 1 for Formalism.FG.FunctionalEquationHom.integralMv_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:37.301301+00:00
-- url     : https://prove2.me/submissions/752b488e-045a-4e74-9155-79a4f69c5c95

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.FunctionalEquationHom
theorem _root_.solution {τ : Type w} {a b : MvPowerSeries τ K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  unfold IntegralMv at ha hb ⊢
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d
end Formalism.FG.FunctionalEquationHom
