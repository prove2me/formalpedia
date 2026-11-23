-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.quad_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:39.965815+00:00
-- url     : https://prove2.me/submissions/4f2255d1-9c07-4b7e-bdeb-de3ac522f690

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MemM_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MemM_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_MemM_mul_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_int_mul

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
theorem _root_.solution {Λ : Submodule R K} {G Y Y' : Matrix (Fin m) (Fin m) K} (hG : ∀ i j, G i j ∈ R)
    (hY : ∀ i j, Y i j ∈ R) (hY' : ∀ i j, Y' i j ∈ R) (hd : MemM Λ (Y - Y')) :
    MemM Λ (Y * G * Y - Y' * G * Y') := by
  have e : Y * G * Y - Y' * G * Y' = (Y - Y') * (G * Y) + Y' * G * (Y - Y') := by
    noncomm_ring
  rw [e]
  exact (hd.mul_right (int_mul hG hY)).add (hd.mul_left (int_mul hY' hG))
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
