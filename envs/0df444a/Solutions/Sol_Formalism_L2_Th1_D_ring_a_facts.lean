-- Prove2me | solution 1 for Formalism.L2.Th1.D.ring_a_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:36:02.426174+00:00
-- url     : https://prove2.me/submissions/8f6a6c48-6b37-4028-b58d-bdd42be81292

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_exists_period
import Theorems.Thm_UpperTheory_Reformulated_B_Qi27_norm_ringA_le


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
namespace Formalism.L2.Th1.D
theorem _root_.solution : RingAFacts := by
  intro l hl
  refine ⟨fun x hx => norm_ringA_le hx, ?_⟩
  intro x hx
  obtain ⟨f, hf, h⟩ := exists_period hx
  refine ⟨f, hf, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, c.2, ?_⟩
  have := congrArg (fun t : ringA l => (t : ℂ_[l])) hc
  simpa using this
end Formalism.L2.Th1.D
