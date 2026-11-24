-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.upK_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:17.23335+00:00
-- url     : https://prove2.me/submissions/e5d29778-fb39-437f-8f50-79e8ad1e20fb

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_diag_mul_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upK_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {U : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kU p) U) :
    uniK (kU p) U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hu := upK_unit h
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := U.invertibleOfIsUnitDet hu
  have hbt : U⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h.2 i j (kU_lt.mpr hij))
  have hz : ∀ a b, kU p a < kU p b → U⁻¹ a b = 0 := fun a b hab => hbt (kU_lt.mp hab)
  refine ⟨⟨fun i => ?_, hz⟩, h1, h2⟩
  have := congrFun (congrFun h1 i) i
  rw [diag_mul_of kU_inj h.2 hz, h.1, one_mul, Matrix.one_apply_eq] at this
  exact this
end Formalism.FourierDecayAlt.P.Ux2
