-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.lowK_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:16.450514+00:00
-- url     : https://prove2.me/submissions/a59a0753-4d78-4300-967f-63370ac3d9b9

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_diag_mul_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowK_unit

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
theorem _root_.solution {L : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kL p) L) :
    uniK (kL p) L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hu := lowK_unit h
  have h1 : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv L hu
  have h2 : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul L hu
  letI := L.invertibleOfIsUnitDet hu
  have hbt : L⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular
      (fun i j hij => h.2 i j (kL_lt.mpr (OrderDual.toDual_lt_toDual.mp hij)))
  have hz : ∀ a b, kL p a < kL p b → L⁻¹ a b = 0 := fun a b hab =>
    hbt (OrderDual.toDual_lt_toDual.mpr (kL_lt.mp hab))
  refine ⟨⟨fun i => ?_, hz⟩, h1, h2⟩
  have := congrFun (congrFun h1 i) i
  rw [diag_mul_of kL_inj h.2 hz, h.1, one_mul, Matrix.one_apply_eq] at this
  exact this
end Formalism.FourierDecayAlt.P.Ux2
