-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.chatA_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:13.549594+00:00
-- url     : https://prove2.me/submissions/5c851918-227f-4c98-b67a-1be1cd7de4fd

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_qminor_inter

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a β : Fin n → ℂ) : chatA E u a β * R = R * chatA E' u a β := by
  unfold chatA
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, qminor_inter E E' R h]
end Formalism.FourierDecayAlt.Q.TInvW
