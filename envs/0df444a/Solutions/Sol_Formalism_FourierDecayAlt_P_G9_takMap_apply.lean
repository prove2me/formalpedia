-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.takMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:47.558955+00:00
-- url     : https://prove2.me/submissions/57ccf718-104c-4a25-ac32-4616f29cd3f6

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
open Module
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) (x : EuclideanSpace ℂ (Fin d)) (i : Fin d) :
    takMap H x i = ∑ j, H i j * conj (x j) := by
  simp [takMap, Matrix.mulVec, dotProduct]
end Formalism.FourierDecayAlt.P.G9
