-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.outer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:38:03.119811+00:00
-- url     : https://prove2.me/submissions/53462aba-f7fb-45a9-993a-f2b3408d3eb6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction

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
theorem _root_.solution {i : Fin (r + 1)} (q : Fin (2 * r + k + 1)) (hq : ∀ c, q ≠ posL k r i c) :
    ∃ a : Fin r, a.val < i.val ∧ (q = eI k r a ∨ q = esI k r a) := by
  have hq' := q.isLt
  have hi := i.isLt
  by_cases h1 : q.val < i.val
  · exact ⟨⟨q.val, by omega⟩, h1, Or.inl (Fin.ext rfl)⟩
  · have h2 : 2 * r + k - i.val < q.val := by
      by_contra h3
      exact hq ⟨q.val - i.val, by unfold mdim; omega⟩ (Fin.ext (by simp only [posL]; omega))
    exact ⟨⟨2 * r + k - q.val, by omega⟩, by simp only; omega, Or.inr (Fin.ext (by simp only [esI]; omega))⟩
end Formalism.FourierDecayAlt.Q.TInvW
