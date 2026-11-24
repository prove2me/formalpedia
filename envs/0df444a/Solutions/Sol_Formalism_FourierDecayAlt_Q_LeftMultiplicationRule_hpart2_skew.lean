-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.hpart2_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:50:42.146798+00:00
-- url     : https://prove2.me/submissions/b5d275ff-c3f9-461b-b149-2e5c124d994e

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
    Hpk k r * (hpart2 (Hpk k r) Z)ᴴ * Hpk k r = -hpart2 (Hpk k r) Z := by
  have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg,
      one_div_neg_eq_neg_one_div]
  simp only [hpart2, hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, mul_smul_comm, smul_mul_assoc,
    mul_add, add_mul, dagdag, hc]
  rw [neg_smul, add_comm (Hpk k r * Zᴴ * Hpk k r) Z]
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
