-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.I_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:18.706494+00:00
-- url     : https://prove2.me/submissions/7b1a28a2-b306-4b26-9153-f4db375ae475

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
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution {R : Subring K} (hc : IsCompact (R : Set K)) (a : K) : IsCompact (I R a) := by
  have : I R a = (fun r => a * r) '' (R : Set K) := by
    ext x; constructor
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, rfl⟩
  rw [this]
  exact hc.image (continuous_const.mul continuous_id)
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
