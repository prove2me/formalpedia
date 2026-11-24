-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lev_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:53:03.852851+00:00
-- url     : https://prove2.me/submissions/491e13b3-55c8-46a1-9725-cf0756c6d882

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_lev_one


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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (n : Mat k r') (hn : IsUnit n.det) : IsUnit (ιLev k 1 r' n).det := by
  have h1 : ιLev k 1 r' n * ιLev k 1 r' n⁻¹ = 1 := by
    rw [← lev_mul, Matrix.mul_nonsing_inv n hn, lev_one]
  exact Matrix.isUnit_det_of_right_inverse h1
end Formalism.FourierDecayAlt.P.LongWeylElement
