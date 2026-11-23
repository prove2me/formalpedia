-- Prove2me | solution 1 for Formalism.FG.HeightVAux.map_liftZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:55.517698+00:00
-- url     : https://prove2.me/submissions/02fdedd7-211e-46a0-8f9d-c09500f5edda

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
theorem _root_.solution {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) :
    map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (liftZ g hg) = g := by
  ext n
  rw [coeff_map]
  rfl
end Formalism.FG.HeightVAux
