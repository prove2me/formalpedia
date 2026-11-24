-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rset_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:27.191416+00:00
-- url     : https://prove2.me/submissions/ffdbc51b-1899-4750-9f8d-47606fdfb821

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_r

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
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {g : B.Mat k (j + ρ)} (hg : g ∈ Rset k j ρ) :
    b11 g = 1 ∧ b21 g = 0 ∧ b31 g = 0 ∧ b22 g = 1 ∧ b32 g = 0 := by
  obtain ⟨_, h1, h2⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext a b
  · have := h1 (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inl (Sum.inl b))) (by rw [eB_ll]; exact b.isLt)
    simpa [b11, Matrix.one_apply] using this
  · have := h1 (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inl b))) (by rw [eB_ll]; exact b.isLt)
    simpa [b21] using this
  · have := h1 (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inl b))) (by rw [eB_ll]; exact b.isLt)
    simpa [b31] using this
  · have hb := b.isLt
    have := h2 (eB k j ρ (Sum.inl (Sum.inr a))) (eB k j ρ (Sum.inl (Sum.inr b))) (by rw [eB_lr]; omega)
      (by rw [eB_lr]; omega) (by rw [eB_lr]; omega)
    simpa [b22, Matrix.one_apply] using this
  · have hb := b.isLt
    have := h2 (eB k j ρ (Sum.inr a)) (eB k j ρ (Sum.inl (Sum.inr b))) (by rw [eB_lr]; omega)
      (by rw [eB_lr]; omega) (by rw [eB_r]; omega)
    simpa [b32] using this
end Formalism.FourierDecayAlt.P.Ux2
