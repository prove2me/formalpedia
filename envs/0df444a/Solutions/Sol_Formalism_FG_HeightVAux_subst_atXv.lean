-- Prove2me | solution 1 for Formalism.FG.HeightVAux.subst_atXv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:55.63044+00:00
-- url     : https://prove2.me/submissions/3066b712-5fbc-481b-8d11-b0c1eb6868c4

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
import Theorems.Thm_Formalism_FG_HeightVAux_hasSubst_vX

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [DecidableEq ι] {τ : Type*}
namespace Formalism.FG.HeightVAux
theorem _root_.solution (G : Fin 2 × ι → MvPowerSeries τ R) (hG : HasSubst G)
    (g : MvPowerSeries ι R) : subst G (atXv g) = subst (fun i => G (0, i)) g := by
  unfold atXv
  rw [subst_comp_subst_apply hasSubst_vX hG]
  congr 1
  funext i
  exact subst_X hG _
end Formalism.FG.HeightVAux
