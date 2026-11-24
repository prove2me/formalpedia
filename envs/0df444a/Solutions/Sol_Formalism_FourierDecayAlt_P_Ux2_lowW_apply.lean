-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.lowW_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:57:13.329813+00:00
-- url     : https://prove2.me/submissions/30cd79b1-c073-4936-858f-d64f572361c8

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
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (a b : Fin p) :
    lowW σ v a b = (if a = b then 1 else 0) + (if h : b < a ∧ σ.symm b < σ.symm a then v ⟨(a, b), h⟩ else 0) := by
  simp [lowW, Matrix.one_apply]
end Formalism.FourierDecayAlt.P.Ux2
