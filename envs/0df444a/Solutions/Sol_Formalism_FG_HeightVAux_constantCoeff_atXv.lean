-- Prove2me | solution 1 for Formalism.FG.HeightVAux.constantCoeff_atXv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:38.188412+00:00
-- url     : https://prove2.me/submissions/ad5748ad-420a-4dfb-a753-209979fb2e16

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
theorem _root_.solution {g : MvPowerSeries ι R} (hg : constantCoeff g = 0) :
    constantCoeff (atXv g) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_vX (fun _ => constantCoeff_X _) hg
end Formalism.FG.HeightVAux
