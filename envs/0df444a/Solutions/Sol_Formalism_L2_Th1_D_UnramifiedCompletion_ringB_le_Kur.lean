-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.ringB_le_Kur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:38.647957+00:00
-- url     : https://prove2.me/submissions/d0774ad9-0e0e-422f-a755-bd46a1f548df

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open UnramifiedCompletion
open Formalism.L2.Th1.D.UnramifiedCompletion
variable {l : ℕ} [hl : Fact l.Prime]
namespace Formalism.L2.Th1.D.UnramifiedCompletion
theorem _root_.solution {x : ℂ_[l]} (hx : x ∈ ringB l) : x ∈ MaximalUnramifiedExtension l := by
  have h1 : ringA l ≤ (MaximalUnramifiedExtension l).toSubring :=
    Subring.closure_le.2 fun z hz => Subfield.le_topologicalClosure _ (Subfield.subset_closure hz)
  exact Subring.topologicalClosure_minimal _ h1 (Subfield.isClosed_topologicalClosure _) hx
end Formalism.L2.Th1.D.UnramifiedCompletion
