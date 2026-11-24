-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.dag_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:29.971795+00:00
-- url     : https://prove2.me/submissions/691ee31e-3573-44a0-aa47-dc24ed0784ec

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_mul_apply


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
theorem _root_.solution (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Mᴴ * Hpk k r) p q =
      WeylGroupFacts.sgn k r p * (star (M (tau k r q) (tau k r p)) * WeylGroupFacts.sgn k r q) := by
  have hs : ∀ i, star (WeylGroupFacts.sgn k r i) = WeylGroupFacts.sgn k r i := by
    intro i; unfold WeylGroupFacts.sgn; split_ifs <;> simp
  have e : Mᴴ * Hpk k r = (Hpk k r * M)ᴴ := by
    rw [Matrix.conjTranspose_mul, Formalism.QuantumDeterminants.GBasic.Hpk_herm]
  rw [mul_assoc, hpk_mul_apply, e, Matrix.conjTranspose_apply, hpk_mul_apply, star_mul', hs]
  ring
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
