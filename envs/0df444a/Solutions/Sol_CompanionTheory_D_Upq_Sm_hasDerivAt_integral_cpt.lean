-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.hasDerivAt_integral_cpt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:03.565212+00:00
-- url     : https://prove2.me/submissions/63051006-bd87-4af4-b98c-d26db789d319

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_continuousOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI CompanionTheory.D.Upq.ModEx
variable {α V : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α] [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure α}
  [IsFiniteMeasureOnCompacts μ]
namespace CompanionTheory.D.Upq.Sm
theorem _root_.solution {F F' : ℝ → α → V} (hF : ∀ t, Continuous (F t))
    (hF' : Continuous fun p : ℝ × α => F' p.1 p.2) (hd : ∀ t a, HasDerivAt (F · a) (F' t a) t)
    {K : Set α} (hK : IsCompact K) (h0 : ∀ a ∉ K, F 0 a = 0)
    (h0' : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ a ∉ K, F' t a = 0) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' 0 a ∂μ) 0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK : IsCompact (Icc (-1 : ℝ) 1 ×ˢ K)).exists_bound_of_continuousOn
    hF'.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Icc (-1 : ℝ) 1)
    (bound := K.indicator fun _ => C) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    ((hF 0).integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0))
    (hF'.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Eventually.of_forall fun a t ht => ?_) ?_ (Eventually.of_forall fun a t _ => hd t a)).2
  · by_cases ha : a ∈ K
    · rw [indicator_of_mem ha]; exact hC (t, a) ⟨ht, ha⟩
    · rw [indicator_of_notMem ha, h0' t ht a ha, norm_zero]
  · exact (integrable_indicator_iff hK.measurableSet).2
      (continuous_const.continuousOn.integrableOn_compact hK)
end CompanionTheory.D.Upq.Sm
