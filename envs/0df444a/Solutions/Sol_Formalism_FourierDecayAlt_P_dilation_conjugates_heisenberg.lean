-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.dilation_conjugates_heisenberg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:02:45.729087+00:00
-- url     : https://prove2.me/submissions/342c10f8-2521-4ae7-b29c-a13bd91ab189

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_heisG_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_dilation_base_vector
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_aDil_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_liftVec_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x7_hb_dil
import Theorems.Thm_Formalism_FourierDecayAlt_P_dilation_mem_group


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open B2x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.DilHeis := by
  intro k r' t ht x
  unfold heis0
  rw [heisG_comm _ (dilation_mem_group k (1 + r') t ht) _ (dilation_base_vector t), Matrix.mul_assoc, aDil_mul_inv _ _ _ ht, Matrix.mul_one,
    aDil_lift, ← liftVec_smul, hb_dil t ht]
end Formalism.FourierDecayAlt.P
