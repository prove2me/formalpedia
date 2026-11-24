-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.glev_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:01.877891+00:00
-- url     : https://prove2.me/submissions/2f1d5c70-75dd-4192-9d2b-45492bc09496

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_inv_fix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := glev_unit hg
  simp only [Glev, UH, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hF⟩ := hg
  refine ⟨?_, fun a ha => ⟨inv_fix hu.2 (hF a ha).1, inv_fix hu.2 (hF a ha).2⟩⟩
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [hu.1, conjTranspose_one, one_mul, mul_one]
end Formalism.FourierDecayAlt.Q.TInvW
