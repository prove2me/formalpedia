-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.MemM.mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:53.884899+00:00
-- url     : https://prove2.me/submissions/c79c2804-e485-46ec-9190-f11b6e86c2f3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace MemM
theorem _root_.solution {Λ : Submodule R K} {A X : Matrix (Fin m) (Fin m) K} (hA : ∀ i j, A i j ∈ R)
    (hX : MemM Λ X) : MemM Λ (X * A) := fun i j => by
  rw [Matrix.mul_apply]
  exact Λ.sum_mem fun k _ => by rw [mul_comm]; exact mul_mem_sub Λ (hA k j) (hX i k)
end MemM
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
