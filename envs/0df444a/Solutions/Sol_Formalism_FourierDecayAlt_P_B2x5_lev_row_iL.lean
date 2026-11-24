-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.lev_row_iL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:03:16.761798+00:00
-- url     : https://prove2.me/submissions/f796048b-e1c1-45d1-9b1a-8fe0b9963f9c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_first_index_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_val

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (iL k r') q = if iL k r' = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg]
  all_goals first | rfl | omega | (simp only [first_index_val, iL_val, lev_val]; omega) | (rw [lev_val]; constructor <;> omega) | (simp_all [Fin.ext_iff] <;> omega)
end Formalism.FourierDecayAlt.P.B2x5
