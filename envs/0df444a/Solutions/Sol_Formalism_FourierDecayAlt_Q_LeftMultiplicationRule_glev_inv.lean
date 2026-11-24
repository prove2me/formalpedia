-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.glev_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:53.428631+00:00
-- url     : https://prove2.me/submissions/006cb3ce-ad0d-445a-936c-0262496a5917

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


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
theorem _root_.solution {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := isUnit_of_uh hg.1
  have key : ∀ b : Fin (2 * r + k + 1) → ℂ, g *ᵥ b = b → g⁻¹ *ᵥ b = b := by
    intro b hb
    calc g⁻¹ *ᵥ b = g⁻¹ *ᵥ (g *ᵥ b) := by rw [hb]
      _ = b := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hg.1, fun a ha => ⟨key _ (hg.2 a ha).1, key _ (hg.2 a ha).2⟩⟩
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
