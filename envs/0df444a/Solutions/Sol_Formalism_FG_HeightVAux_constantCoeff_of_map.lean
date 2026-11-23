-- Prove2me | solution 1 for Formalism.FG.HeightVAux.constantCoeff_of_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:38.65393+00:00
-- url     : https://prove2.me/submissions/3631e029-df00-4d0f-a524-186b59afba8a

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.HeightVAux
open MvPowerSeries Formalism.G Formalism.LT
variable {l : ℕ} [Fact l.Prime]
namespace Formalism.FG.HeightVAux
theorem _root_.solution {σ : Type*} (x : MvPowerSeries σ ℤ_[l])
    (hx : constantCoeff (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x) = 0) :
    constantCoeff x = 0 := by
  rw [constantCoeff_map] at hx
  exact Subtype.ext hx
end Formalism.FG.HeightVAux
