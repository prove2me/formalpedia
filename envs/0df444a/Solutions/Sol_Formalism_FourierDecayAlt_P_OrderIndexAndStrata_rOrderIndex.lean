-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrderIndexAndStrata.rOrderIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:08.270979+00:00
-- url     : https://prove2.me/submissions/2d0a36a7-6c47-4f1a-8b69-320cf87e95a4

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
theorem _root_.solution : ROrderIndex := by
  intro o _ _ _
  have hs : Function.Surjective ((IsLocalRing.residue o).comp
      ((RingHom.fst o o).comp (ROrd o).subtype)) := by
    intro y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨⟨(a, a), by simp [ROrd]⟩, rfl⟩
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata
