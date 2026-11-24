-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.geom_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:17.955123+00:00
-- url     : https://prove2.me/submissions/8c93dfb8-12dc-42de-b6ed-ca083f80b0a4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_isClosed_ringB

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
theorem _root_.solution {w : ℂ_[l]} (hw : w ∈ ringB l) (h : ‖w‖ < 1) : (1 - w)⁻¹ ∈ ringB l := by
  have h1 := (hasSum_geometric_of_norm_lt_one h).tendsto_sum_nat
  exact isClosed_ringB.mem_of_tendsto h1
    (Eventually.of_forall fun n => sum_mem fun i _ => pow_mem hw i)
end Formalism.L2.Th1.D.UnramifiedCompletion
