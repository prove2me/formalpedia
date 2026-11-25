-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:17.511083+00:00
-- url     : https://prove2.me/submissions/0f939b3e-c783-47b0-b639-6b7803856640

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_subst
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_swp

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
variable {f : ι → MvPowerSeries ι R} {F : ι → MvPowerSeries (Fin 2 × ι) R}
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution (hf : IsIdMod2 f) (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) : IsCommV F := by
  have h : (fun i => subst swp (F i)) = F := by
    refine inj hf (fun i => cc_subst cc_swp (hF0 i)) hF0 fun j => ?_
    rw [key hF0 hFG swp cc_swp, hFG, add_comm (atXv (f j))]
    rfl
  intro i
  exact congrFun h i
end Formalism.FG.FormalGroupCoefficients
