-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:21.680141+00:00
-- url     : https://prove2.me/submissions/e52cb415-4e21-463b-9bb8-6b188c803fdb

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsX
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hsY

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
theorem _root_.solution (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) {τ : Type*}
    (b : Fin 2 × ι → MvPowerSeries τ R) (hb : ∀ x, constantCoeff (b x) = 0) (j : ι) :
    subst (fun i => subst b (F i)) (f j) =
      subst (fun i => b ((0 : Fin 2), i)) (f j) + subst (fun i => b ((1 : Fin 2), i)) (f j) := by
  rw [← subst_comp_subst_apply (hs hF0) (hs hb), hFG, subst_add (hs hb), atXv, atYv,
    subst_comp_subst_apply hsX (hs hb), subst_comp_subst_apply hsY (hs hb)]
  simp only [vX, vY, subst_X (hs hb)]
end Formalism.FG.FormalGroupCoefficients
