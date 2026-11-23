-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.innerXYOfReduced
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:44.909516+00:00
-- url     : https://prove2.me/submissions/2b76b9a0-b4c8-40a2-87f6-b5cc94a75fea

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
theorem _root_.solution : InnerXYOfReduced := by
  intro hOm hRI hSplit hAmp m β t c ht V _ _ _ Φ hint
  have hmp := (hSplit m β).2
  have i1 : PolishSpace (XY m) := inferInstance
  have i2 : StandardBorelSpace (XY m) := inferInstance
  have i3 : SecondCountableTopology (RedCoord m) := inferInstance
  have i4 : MeasurableSpace.CountablyGenerated (RedCoord m) := inferInstance
  have i5 : MeasurableSpace.CountablySeparated (RedCoord m) := inferInstance
  have hemb : MeasurableEmbedding (redOf m) := hmp.measurable.measurableEmbedding (hSplit m β).1.injective
  have hfun : (fun p : XY m =>
      psi β (g0 ((-1) ^ (m + 3) * (c * t ^ (m + 1))) p.1 / t) • amp β m Φ (c * t ^ (m + 1)) t p) =
      redIntegrand β m Φ (c * t ^ (m + 1)) t ∘ redOf m :=
    funext fun p => hAmp m β (c * t ^ (m + 1)) t ht V Φ p
  have h1 := hRI m β t c ht V Φ hint
  have h2 := hOm m β t c ht V Φ hint
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hmp.integrable_comp_emb hemb).2 h1
  · rw [h2, hfun]
    exact (hmp.integral_comp hemb _).symm
end Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
