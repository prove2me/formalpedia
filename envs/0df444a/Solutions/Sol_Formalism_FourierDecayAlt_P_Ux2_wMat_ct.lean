-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.wMat_ct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:36.921491+00:00
-- url     : https://prove2.me/submissions/5eef9dba-199f-44e3-a18c-e586b82c493b

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
theorem _root_.solution (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by
  ext a b
  by_cases h : b = a.rev
  · subst h; simp [G.wMat, conjTranspose_apply]
  · have h' : a ≠ b.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [G.wMat, conjTranspose_apply, h, h']
end Formalism.FourierDecayAlt.P.Ux2
