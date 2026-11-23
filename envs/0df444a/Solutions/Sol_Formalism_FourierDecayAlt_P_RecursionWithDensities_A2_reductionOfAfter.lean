-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A2.reductionOfAfter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:09.259728+00:00
-- url     : https://prove2.me/submissions/731c6c28-59b2-46b0-81d6-ae4b394a31c2

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A2_domAfterA_of_old

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism.FourierDecayAlt.P.BudgetLiftBounds Formalism.FourierDecayAlt.TC
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
theorem _root_.solution : ReductionOfAfter := by
  intro hR C₀ h0
  obtain ⟨C', C, hC⟩ := hR C₀ h0
  refine ⟨C', C, ?_⟩
  intro E _ _ H _ _ _ W _ len Kl f Θ D Pat1 Pat3 _ pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 hA13 hE
  exact hC E H W len Kl f Θ D Pat1 Pat3 pat1 pat3 c1 c3 ep1 ep3 bd4 Φ tr w0 V jn ρ c
    hKl hf hΘ hr hK hA2 (domAfterA_of_old D hA13) hE
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A2
