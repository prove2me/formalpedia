-- Prove2me | solution 1 for Formalism.FG.HeightVAux.coe_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:37.905135+00:00
-- url     : https://prove2.me/submissions/093aa7b2-af1d-4cec-8112-e05e1cc6fe27

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
theorem _root_.solution {σ : Type*} :
    Function.Injective (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) :
      MvPowerSeries σ ℤ_[l] → MvPowerSeries σ ℚ_[l]) := by
  intro a b hab
  ext n
  have := congrArg (coeff n) hab
  rw [coeff_map, coeff_map] at this
  exact Subtype.ext this
end Formalism.FG.HeightVAux
