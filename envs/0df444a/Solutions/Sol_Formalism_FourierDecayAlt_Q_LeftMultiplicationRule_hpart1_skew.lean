-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.hpart1_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:34.532809+00:00
-- url     : https://prove2.me/submissions/dc03bf21-bf03-41d9-aa78-61a3f71d6579

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_hinv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_dagdag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution (Z : Mx k r) :
    Hpk k r * (hpart1 (Hpk k r) Z)ᴴ * Hpk k r = -hpart1 (Hpk k r) Z := by
  simp only [hpart1, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, mul_smul_comm, smul_mul_assoc,
    mul_sub, sub_mul, dagdag]
  ext i j
  simp
  ring
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
