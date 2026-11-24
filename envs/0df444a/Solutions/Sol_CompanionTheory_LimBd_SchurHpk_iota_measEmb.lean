-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.iota_measEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:31:36.506887+00:00
-- url     : https://prove2.me/submissions/39ed2e1b-26f2-4067-8ba9-9b59efbb3bf3

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution (hP : IsCayley k r ε P) : MeasurableEmbedding (iota (ε := ε) P) :=
  (iota_closedEmb hP).measurableEmbedding
end CompanionTheory.LimBd.SchurHpk
