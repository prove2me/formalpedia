-- Prove2me | solution 1 for Formalism.IndefR.Tow.SobPf.Avg.hasFDerivAt_integral_pIter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:45.431333+00:00
-- url     : https://prove2.me/submissions/cf902f37-f71d-4b8d-8171-99f44c6a2160

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
import Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_ae_mem_of_compl
import Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_aesm_of_continuousOn
import Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_pIter_contOn_slice
import Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_hasFDerivAt_pIter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open Formalism Formalism.IndefR Formalism.IndefR.Tow Formalism.IndefR.Tow.SobPf Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Formalism.IndefR.Tow.SobPf.Avg
theorem _root_.solution {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} (hK : IsCompact K)
    (hKm : MeasurableSet K) (hμK : μ Kᶜ = 0) {Φ : (Fin m → ℝ) → X → E}
    (hΦ : ∀ k ∈ K, ContDiff ℝ ∞ fun t => Φ t k)
    (hc : ∀ j : ℕ, ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K))
    (j : ℕ) (t₀ : Fin m → ℝ) :
    HasFDerivAt (fun t => ∫ k, pIter Φ j t k ∂μ)
      (∫ k, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E (pIter Φ (j + 1) t₀ k) ∂μ)
      t₀ := by
  have hae : ∀ᵐ k ∂μ, k ∈ K := ae_mem_of_compl hμK
  have hsm : ∀ (i : ℕ) (t : Fin m → ℝ),
      AEStronglyMeasurable (fun k => pIter Φ i t k) μ := fun i t =>
    aesm_of_continuousOn hKm hμK (pIter_contOn_slice (hc i) t)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ 1).prod hK).exists_bound_of_continuousOn
    ((hc (j + 1)).mono (Set.prod_mono (Set.subset_univ _) subset_rfl))
  obtain ⟨C₀, hC₀⟩ :=
    hK.exists_bound_of_continuousOn (pIter_contOn_slice (hc j) t₀)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun t k => pIter Φ j t k)
    (F' := fun t k => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Fin m → ℝ) E
      (pIter Φ (j + 1) t k))
    (bound := fun _ => C) (s := ball t₀ 1) (ball_mem_nhds t₀ zero_lt_one) ?_ ?_ ?_ ?_ (integrable_const C) ?_
  · filter_upwards with t using hsm j t
  · exact Integrable.mono' (integrable_const C₀) (hsm j t₀)
      (by filter_upwards [hae] with k hk using hC₀ k hk)
  · exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hsm (j + 1) t₀)
  · filter_upwards [hae] with k hk t ht
    exact (LinearIsometryEquiv.norm_map _ _).trans_le
      (hC (t, k) (Set.mk_mem_prod (ball_subset_closedBall ht) hk))
  · filter_upwards [hae] with k hk t _
    exact hasFDerivAt_pIter (hΦ k hk) j t
end Formalism.IndefR.Tow.SobPf.Avg
