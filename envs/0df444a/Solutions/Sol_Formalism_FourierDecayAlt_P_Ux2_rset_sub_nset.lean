-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rset_sub_nset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:14.918065+00:00
-- url     : https://prove2.me/submissions/759669fc-af6b-47e6-a304-789a29f20164

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose

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
theorem _root_.solution : Rset k j ρ ⊆ Nset k (j + ρ) := by
  rintro g ⟨hG, h1, h2⟩
  refine ⟨hG, ?_, ?_⟩
  · intro a i hai
    by_cases ha : a.val < j
    · exact h1 i (eI k (j + ρ) a) ha
    · have hai' : a.val ≤ i.val := hai
      have := a.isLt
      exact h2 i (eI k (j + ρ) a) (show j ≤ a.val by omega) (show a.val < j + (2 * ρ + k + 1) by omega) (by omega)
  · intro i b hb1 hb2 hi
    exact h2 i b (by omega) (by omega) (by omega)
end Formalism.FourierDecayAlt.P.Ux2
