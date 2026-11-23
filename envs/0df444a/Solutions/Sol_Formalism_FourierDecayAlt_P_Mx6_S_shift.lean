-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.S_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:18.608283+00:00
-- url     : https://prove2.me/submissions/14117c81-65a4-48d0-bb03-6d98cee968d3

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_kap_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_kap_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6
theorem _root_.solution (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    kap P g * SS P l = SS P l * kap P f := by
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]
end Formalism.FourierDecayAlt.P.Mx6
