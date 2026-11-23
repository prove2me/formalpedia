-- Prove2me | solution 1 for Formalism.FG.HeightVAux.atYv_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:37.898805+00:00
-- url     : https://prove2.me/submissions/d4b18959-ffe4-4659-8b7d-d85d0ad0285b

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
import Theorems.Thm_Formalism_FG_HeightVAux_hasSubst0
import Theorems.Thm_Formalism_FG_HeightVAux_hasSubst_vY

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
theorem _root_.solution (h : ι → MvPowerSeries ι R) (hh : ∀ i, constantCoeff (h i) = 0)
    (g : MvPowerSeries ι R) : atYv (subst h g) = subst (fun i => atYv (h i)) g := by
  unfold atYv
  rw [subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vY]
end Formalism.FG.HeightVAux
