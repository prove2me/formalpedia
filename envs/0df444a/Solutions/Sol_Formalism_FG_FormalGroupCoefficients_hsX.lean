-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.hsX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:24.115933+00:00
-- url     : https://prove2.me/submissions/85342948-e5f8-4533-bbae-24ec3fc0c5f4

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_X

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
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution : HasSubst (fun i : ι => (vX i : MvPowerSeries (Fin 2 × ι) R)) :=
  hs fun _ => cc_X _
end Formalism.FG.FormalGroupCoefficients
