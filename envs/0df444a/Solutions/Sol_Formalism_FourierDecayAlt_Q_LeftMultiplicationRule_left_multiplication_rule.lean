-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.left_multiplication_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:37:38.051892+00:00
-- url     : https://prove2.me/submissions/b6c13ee5-2d4e-45d8-baaf-6e94190ce98c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_LeftMultiplicationRule
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_posL_in
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_case1
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_case2
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LeftMultiplicationRule_case3

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
theorem _root_.solution : RuleLeft := by
  intro E _ _ k r z l D f hz _ _ _ hL c hc g₁ hg₁ hgD
  refine ⟨fun j => ?_, fun j => ?_, case3 hz hL hc hg₁ hgD⟩
  · exact case1 hz hL hc hg₁ hgD _ (posL_in l j)
  · exact case2 hz hL hc hg₁ hgD _ (posL_in l j)
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
