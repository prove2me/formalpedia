-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.continuous_psiH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:43.233003+00:00
-- url     : https://prove2.me/submissions/1e183a23-aa20-4da9-8aa3-c3a81f84b27e

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_continuous_cornerB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
namespace Formalism.FourierDecayAlt.P.Ux13
theorem _root_.solution {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) :
    Continuous fun η : XiH p s σ => psiH β σ η := by
  have h1 : Continuous fun η : XiH p s σ => subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) :=
    continuous_subS.comp ((continuous_const.matrix_mul
      ((continuous_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul continuous_const)
  have h2 : Continuous fun η : XiH p s σ => supS (G.upper η.2.2) :=
    continuous_supS.comp (continuous_upper.comp (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun η : XiH p s σ => cornerA η.1.1 :=
    continuous_cornerA.comp (continuous_fst.comp continuous_fst)
  have h4 : Continuous fun η : XiH p s σ => cornerB η.1.2 :=
    continuous_cornerB.comp (continuous_snd.comp continuous_fst)
  simp only [psiH, G.psi]
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (((h1.add h2).add h3).add h4)))))
end Formalism.FourierDecayAlt.P.Ux13
