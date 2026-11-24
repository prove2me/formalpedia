-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.second_capelli_minor_intertwines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:03.780634+00:00
-- url     : https://prove2.me/submissions/ade0323c-6fc0-4143-add0-a2ed01229811

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
    (a a' β β' : Fin n → ℂ) : chat2A E u a a' β β' * R = R * chat2A E' u a a' β β' := by
  unfold chat2A
  simp only [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero, smul_mul_assoc,
    mul_smul_comm, qminor_inter E E' R h]
end Formalism.FourierDecayAlt.Q.TInvW
