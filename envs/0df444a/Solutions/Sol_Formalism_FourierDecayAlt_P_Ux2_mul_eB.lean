-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.mul_eB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:28:49.769144+00:00
-- url     : https://prove2.me/submissions/07763e78-37de-401a-9d60-3ea943fc76ab

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
theorem _root_.solution (M N : B.Mat k (j + ρ)) (x y : Ix k j ρ) :
    (M * N) (eB k j ρ x) (eB k j ρ y) =
      ∑ z : Ix k j ρ, M (eB k j ρ x) (eB k j ρ z) * N (eB k j ρ z) (eB k j ρ y) := by
  rw [Matrix.mul_apply]
  exact (Equiv.sum_comp (eB k j ρ) (fun z => M (eB k j ρ x) z * N z (eB k j ρ y))).symm
end Formalism.FourierDecayAlt.P.Ux2
