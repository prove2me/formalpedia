-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.herm_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:13:02.284948+00:00
-- url     : https://prove2.me/submissions/8a6594f9-5b50-45f7-84ed-c4f426aae1fd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_sum_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_liftVec_levPos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_liftVec_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_Hpk_levPos

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (liftVec k 1 r' y) (liftVec k 1 r' y') = herm (Hpk k r') y y' := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  rw [sum_lift]
  · apply Finset.sum_congr rfl; intro i _
    rw [liftVec_levPos, sum_lift]
    · congr 1
      apply Finset.sum_congr rfl; intro j _
      rw [liftVec_levPos, Hpk_levPos]
    · intro p hp; rw [liftVec_out k r' y p hp, mul_zero]
  · intro p hp; rw [liftVec_out k r' y' p hp, star_zero, zero_mul]
end Formalism.FourierDecayAlt.P.B2x4
