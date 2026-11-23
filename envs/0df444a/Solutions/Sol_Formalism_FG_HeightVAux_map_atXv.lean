-- Prove2me | solution 1 for Formalism.FG.HeightVAux.map_atXv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:54.966813+00:00
-- url     : https://prove2.me/submissions/dcede078-164e-4b95-a288-33d34595c462

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
theorem _root_.solution {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atXv g) = atXv (map φ g) := by
  unfold atXv
  rw [map_subst hasSubst_vX]
  congr 1
  funext i
  exact map_X φ _
end Formalism.FG.HeightVAux
