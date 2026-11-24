-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.uwb_eq_emb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:36:37.517994+00:00
-- url     : https://prove2.me/submissions/4b175550-72a7-489f-8ea0-d88538e3f436

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_midx
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_uwb_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_uwb_row

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution {g : Mat k r} (hg : g ∈ UWb k r) : g = embWb k r (g.submatrix (wI k r) (wI k r)) := by
  ext i j
  by_cases hj : mid k r j
  · by_cases hi : mid k r i
    · rw [emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]
    · rw [emb_out_row _ i j hi, uwb_row hg i j hi]
  · rw [emb_out_col _ i j hj, uwb_col hg j i hj]
end Formalism.FourierDecayAlt.P.B2x3
