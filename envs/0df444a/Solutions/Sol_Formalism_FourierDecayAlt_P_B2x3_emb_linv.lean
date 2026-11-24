-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.emb_linv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:03:20.807608+00:00
-- url     : https://prove2.me/submissions/e0ea3e02-dcab-4528-9f1c-4baafc15a0f1

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_Em
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_Q

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
theorem _root_.solution (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (Em k r)ᵀ * embWb k r a * Em k r = a := by
  rw [emb_eq, Matrix.mul_add, Matrix.add_mul, EmT_Q, Matrix.zero_mul, add_zero]
  calc (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = ((Em k r)ᵀ * Em k r) * a * ((Em k r)ᵀ * Em k r) := by
        simp only [Matrix.mul_assoc]
    _ = a := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.B2x3
