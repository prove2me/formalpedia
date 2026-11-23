-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderChainWeights.mem_ROrd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:18.221526+00:00
-- url     : https://prove2.me/submissions/30a3eac8-f97a-4b9e-a5bb-542127814914

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderChainWeights

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderChainWeights
open Matrix Finset MeasureTheory
open Formalism.FourierDecayAlt.S3
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.OrderChainWeights
theorem _root_.solution {o : Type} [CommRing o] [IsLocalRing o] (p : o × o) :
    p ∈ ROrd o ↔ IsLocalRing.residue o p.1 = IsLocalRing.residue o p.2 := by
  unfold ROrd
  rw [RingHom.mem_eqLocus]
  rfl
end Formalism.FourierDecayAlt.P.OrderChainWeights
