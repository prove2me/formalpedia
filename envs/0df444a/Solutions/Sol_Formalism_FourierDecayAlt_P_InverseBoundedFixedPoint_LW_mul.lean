-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.LW.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:58:13.169733+00:00
-- url     : https://prove2.me/submissions/8374676f-64a4-49fd-b279-248325e6b68e

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
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace LW
theorem _root_.solution {f g : (Fin m → K) → K} (hf : LW R c f) (hg : LW R c g) :
    LW R c (fun v => f v * g v) :=
  ⟨fun v hv => R.mul_mem (hf.1 v hv) (hg.1 v hv), fun Λ v v' hv hv' hd => by
    have := (sm c Λ).add_mem (mul_mem_sub _ (hf.1 v hv) (hg.2 Λ v v' hv hv' hd))
      (mul_mem_sub _ (hg.1 v' hv') (hf.2 Λ v v' hv hv' hd))
    have e : f v * g v - f v' * g v' = f v * (g v - g v') + g v' * (f v - f v') := by ring
    rw [e]; exact this⟩
end LW
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
