-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.upper_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:36:35.042622+00:00
-- url     : https://prove2.me/submissions/dd4d1cc2-40da-431d-ad33-696c460f8a22

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kU_lt

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
theorem _root_.solution (u : G.UT p → ℂ) : uniK (kU p) (G.upper u) := by
  refine ⟨fun i => by simp [G.upper, G.strictUpper], fun a b hab => ?_⟩
  rw [kU_lt] at hab
  simp [G.upper, G.strictUpper, not_lt.mpr hab.le, ne_of_gt hab]
end Formalism.FourierDecayAlt.P.Ux2
