-- Prove2me | solution 1 for Formalism.FG.CongrVAux.zd_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.112312+00:00
-- url     : https://prove2.me/submissions/4095911a-daf5-4ed2-90a2-7c85bc4c75aa

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_CongrVAux_zd_add
import Theorems.Thm_Formalism_FG_CongrVAux_zd_mul_left

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
variable {R : Type u} [CommRing R] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution {d : τ →₀ ℕ} {a a' b b' : MvPowerSeries τ R} (ha : Zd d (a - a'))
    (hb : Zd d (b - b')) : Zd d (a * b - a' * b') := by
  have e : a * b - a' * b' = b * (a - a') + a' * (b - b') := by ring
  rw [e]
  exact zd_add (zd_mul_left _ ha) (zd_mul_left _ hb)
end Formalism.FG.CongrVAux
