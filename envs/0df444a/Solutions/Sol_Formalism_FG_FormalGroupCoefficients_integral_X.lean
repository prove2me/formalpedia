-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.integral_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:36.417387+00:00
-- url     : https://prove2.me/submissions/ce208441-1b17-477e-919c-9bed0647d320

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV

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
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution {τ : Type*} (x : τ) : IntegralMv (X x : MvPowerSeries τ K) := fun d => by
  classical
  rw [coeff_X]
  split_ifs <;> simp
end Formalism.FG.FormalGroupCoefficients
