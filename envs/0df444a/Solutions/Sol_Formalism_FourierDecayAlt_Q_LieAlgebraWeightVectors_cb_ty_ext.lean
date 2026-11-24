-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_ty_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:15.163841+00:00
-- url     : https://prove2.me/submissions/a0a650aa-390a-41a7-a4a0-effd0a546009

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_eq__0ffcd36dceb3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution (Q : M.Par) {π π' : M.Ty Q}
    (h : ∀ j : Fin (Q.k - 1), M.rho Q π (j.1 + 1) = M.rho Q π' (j.1 + 1)) : π = π' := by
  funext j
  apply Fin.ext
  have e := h j
  rw [cb_rho_eq' Q π j, cb_rho_eq' Q π' j] at e
  exact_mod_cast add_left_cancel e
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
