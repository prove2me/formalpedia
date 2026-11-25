-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.inv_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:36:49.006123+00:00
-- url     : https://prove2.me/submissions/6c1e6e54-f324-47a1-8d07-d2ce51c677ab

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {m : ℝ} (h : EB A m) :
    EB A⁻¹ ((n - 1).factorial * m ^ (n - 1) / ‖A.det‖) := by
  intro i j
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Matrix.adjugate_fin_succ_eq_det_submatrix,
      norm_mul]
    have h1 : ‖((-1 : ℂ) ^ ((j : ℕ) + (i : ℕ)))‖ = 1 := by simp
    rw [h1, one_mul]
    have h2 : ‖(A.submatrix j.succAbove i.succAbove).det‖ ≤ n.factorial * m ^ n := by
      have := det_norm_le (A.submatrix j.succAbove i.succAbove) (m := m) (fun a b => h _ _)
      simpa using this
    rw [Ring.inverse_eq_inv', norm_inv]
    simp only [Nat.add_sub_cancel]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (norm_nonneg _))
end Formalism.FourierDecayAlt.P.Ux5
