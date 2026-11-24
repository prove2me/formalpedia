-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.uniK_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:10.666807+00:00
-- url     : https://prove2.me/submissions/6a92c3ca-9964-437c-bbbd-5b09cdb28540

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_diag_mul_of

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
theorem _root_.solution {κ : Fin p → ℤ} (hκ : Function.Injective κ) {M N : Matrix (Fin p) (Fin p) ℂ}
    (hM : uniK κ M) (hN : uniK κ N) : uniK κ (M * N) := by
  refine ⟨fun i => by rw [diag_mul_of hκ hM.2 hN.2, hM.1, hN.1, one_mul], fun a b hab => ?_⟩
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : κ a < κ c
  · rw [hM.2 a c h, zero_mul]
  · rw [hN.2 c b (lt_of_le_of_lt (not_lt.mp h) hab), mul_zero]
end Formalism.FourierDecayAlt.P.Ux2
