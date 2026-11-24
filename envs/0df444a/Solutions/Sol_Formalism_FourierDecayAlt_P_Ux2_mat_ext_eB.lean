-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.mat_ext_eB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:52.687602+00:00
-- url     : https://prove2.me/submissions/82c7fd3c-7d45-40d8-85ec-3f986ba8a3a5

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
theorem _root_.solution {M N : B.Mat k (j + ρ)}
    (h : ∀ x y, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) : M = N := by
  ext a b
  simpa using h ((eB k j ρ).symm a) ((eB k j ρ).symm b)
end Formalism.FourierDecayAlt.P.Ux2
