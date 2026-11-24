-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_rho_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:52:16.488577+00:00
-- url     : https://prove2.me/submissions/156fbf57-1394-489c-870d-219231628d4d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (Q : M.Par) (c : ℝ) (τ : M.Ty Q) (j : Fin (Q.k - 1))
    (h : ∃ n : ℤ, Q.lo (j.1 + 1) - c = n) : ∃ n : ℤ, M.rho Q τ (j.1 + 1) - c = n := by
  rw [cb_rho_eq' Q τ j]
  obtain ⟨n, hn⟩ := h
  exact ⟨n + ((τ j : Fin _) : ℕ), by push_cast; linarith⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
