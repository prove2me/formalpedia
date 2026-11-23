-- Prove2me | solution 1 for Formalism.FG.CongrVAux.divBy_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:21.947205+00:00
-- url     : https://prove2.me/submissions/c93d9fc6-4911-420e-ad3c-be9931a526e1

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_LT_CoeffP_Bd_mul


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
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {c : K} {a a' b b' : MvPowerSeries τ K} (ha' : IntegralMv a')
    (hb : IntegralMv b) (hab : DivByMv c (a - a')) (hbb : DivByMv c (b - b')) :
    DivByMv c (a * b - a' * b') := by
  have e : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  intro d
  rw [e, map_add]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · simpa using (Formalism.LT.CoeffP.Bd.mul hab hb (norm_nonneg c) zero_le_one) d
  · simpa using (Formalism.LT.CoeffP.Bd.mul ha' hbb zero_le_one (norm_nonneg c)) d
end Formalism.FG.CongrVAux
