-- Prove2me | solution 1 for Formalism.FG.HeightVAux.dvd_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:38.81144+00:00
-- url     : https://prove2.me/submissions/b9e4ed8b-1b42-43a5-98c6-3e44d7a5792a

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
theorem _root_.solution {x : ℤ_[l]}
    (hx : ‖(PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x‖ ≤ ‖((l : ℕ) : ℚ_[l])‖) :
    (l : ℤ_[l]) ∣ x :=
  (PadicInt.norm_lt_one_iff_dvd x).mp (lt_of_le_of_lt hx Padic.norm_p_lt_one)
end Formalism.FG.HeightVAux
