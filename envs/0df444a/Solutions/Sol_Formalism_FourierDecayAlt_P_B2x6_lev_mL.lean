-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.lev_mL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:03.324262+00:00
-- url     : https://prove2.me/submissions/7729faa3-a2fc-412b-be62-8ff0b461ed28

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution (g : Mat k r') (i : Fin (2 * r' + k + 1)) : ιLev k 1 r' g (lv k r' i) (iL k r') = 0 := by
  have := i.isLt
  unfold ιLev; rw [dif_pos (by rw [lv_val]; omega), dif_neg (by rw [iL_val]; omega)]
end Formalism.FourierDecayAlt.P.B2x6
