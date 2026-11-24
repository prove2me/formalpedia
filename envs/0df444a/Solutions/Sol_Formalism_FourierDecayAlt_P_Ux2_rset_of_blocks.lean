-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rset_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:29:28.233141+00:00
-- url     : https://prove2.me/submissions/7f381e31-c7fe-4e90-81a3-614e2c5c5a90

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
theorem _root_.solution {g : B.Mat k (j + ρ)} (hG : g ∈ B.GV k (j + ρ)) (h11 : b11 g = 1) (h21 : b21 g = 0)
    (h31 : b31 g = 0) (h22 : b22 g = 1) (h32 : b32 g = 0) : g ∈ Rset k j ρ := by
  refine ⟨hG, ?_, ?_⟩
  · intro i b hb
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
    rcases y with (y|y)|y
    · rcases x with (x|x)|x
      · have := congrFun (congrFun h11 x) y; simpa [b11, Matrix.one_apply] using this
      · have := congrFun (congrFun h21 x) y; simpa [b21] using this
      · have := congrFun (congrFun h31 x) y; simpa [b31] using this
    · rw [eB_lr] at hb; omega
    · rw [eB_r] at hb; omega
  · intro i b hb1 hb2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective b
    rcases y with (y|y)|y
    · rw [eB_ll] at hb1; have := y.isLt; omega
    · rcases x with (x|x)|x
      · rw [eB_ll] at hi; have := x.isLt; omega
      · have := congrFun (congrFun h22 x) y; simpa [b22, Matrix.one_apply] using this
      · have := congrFun (congrFun h32 x) y; simpa [b32] using this
    · rw [eB_r] at hb2; omega
end Formalism.FourierDecayAlt.P.Ux2
