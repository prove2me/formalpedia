-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.norm_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:54.06433+00:00
-- url     : https://prove2.me/submissions/7a0f7954-97c9-41c8-9c63-82e4aff9c5ac

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_integrable_of_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)
variable {μ e}
omit [IsTopologicalGroup G]
namespace CompanionTheory.D.gk.admitted.PrismTransfer
theorem _root_.solution [SecondCountableTopology K] (he : Continuous e) {f : K → ℂ} {δ : ℝ} (hf : ∀ k, ‖f k‖ ≤ δ) :
    ‖∫ k, e k * f k ∂μ‖ ≤ (∫ k, ‖e k‖ ∂μ) * δ := by
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (integrable_of_cont (by fun_prop)) (ae_of_all _ fun k => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hf k) (norm_nonneg _)
end CompanionTheory.D.gk.admitted.PrismTransfer
