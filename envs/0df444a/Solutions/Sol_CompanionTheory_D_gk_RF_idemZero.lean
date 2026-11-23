-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.idemZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:24.315922+00:00
-- url     : https://prove2.me/submissions/a34977df-4eb4-484c-b45d-44c4cf8e9c46

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
namespace CompanionTheory.D.gk.RF
theorem _root_.solution : IdemZero := by
  intro A _ Q hc hq ht
  have key : ∀ s, ‖Q s‖ < 1 → Q s = 0 := fun s h => by
    have h1 : ‖Q s‖ ≤ ‖Q s‖ * ‖Q s‖ := by conv_lhs => rw [← hq s]
                                          exact norm_mul_le _ _
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (Q s)])
  have hcl : IsClopen {s | Q s = 0} := ⟨isClosed_eq hc continuous_const, by
    have : {s | Q s = 0} = {s | ‖Q s‖ < 1} := Set.ext fun s => ⟨fun h => by simp [show Q s = 0 from h], key s⟩
    rw [this]; exact isOpen_lt hc.norm continuous_const⟩
  obtain ⟨s₀, hs₀⟩ := ((tendsto_zero_iff_norm_tendsto_zero.1 ht).eventually (gt_mem_nhds one_pos)).exists
  intro s
  exact (hcl.eq_univ ⟨s₀, key s₀ hs₀⟩).ge (Set.mem_univ s)
end CompanionTheory.D.gk.RF
