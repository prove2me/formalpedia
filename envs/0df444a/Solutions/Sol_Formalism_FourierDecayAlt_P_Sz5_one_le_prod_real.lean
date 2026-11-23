-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.one_le_prod_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:55.613566+00:00
-- url     : https://prove2.me/submissions/cc2ca031-494d-49b5-ac13-6099a8774a86

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution {α : Type} (s : Finset α) (f : α → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  have h1 : ∏ i ∈ s, (1:ℝ) ≤ ∏ i ∈ s, f i :=
    Finset.prod_le_prod (fun i _ => zero_le_one) h
  simpa using h1
end Formalism.FourierDecayAlt.P.Sz5
