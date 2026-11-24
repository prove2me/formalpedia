-- Prove2me | solution 1 for Formalism.IndefR.Tow.SobPf.Avg.contDiff_integral_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:43:48.282043+00:00
-- url     : https://prove2.me/submissions/4443650d-90f2-4990-9932-26cf450eb26a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_SobolevIteration_HasFDerivAtIntegralPIter
import Theorems.Thm_Formalism_IndefR_Tow_SobPf_Avg_hasFDerivAt_integral_pIter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
namespace Formalism.IndefR.Tow.SobPf.Avg
variable {m : ℕ} {X E : Type*} [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private theorem integral_linearIsometryEquiv_comp {α F G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F ≃ₗᵢ[ℝ] G) (φ : α → F) :
    ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toContinuousLinearEquiv.integral_comp_comm φ
end Formalism.IndefR.Tow.SobPf.Avg
end
end

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
    (hc : ∀ j : ℕ, ContinuousOn (fun q : (Fin m → ℝ) × X => pIter Φ j q.1 q.2) (Set.univ ×ˢ K)) :
    (∀ j : ℕ, iteratedFDeriv ℝ j (fun t => ∫ k, Φ t k ∂μ) = fun t => ∫ k, pIter Φ j t k ∂μ) ∧
      ContDiff ℝ ∞ (fun t => ∫ k, Φ t k ∂μ) := by
  have key : ∀ j : ℕ, iteratedFDeriv ℝ j (fun t => ∫ k, Φ t k ∂μ) =
      fun t => ∫ k, pIter Φ j t k ∂μ := by
    intro j
    induction j with
    | zero =>
      funext t
      simp only [pIter, iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      rw [integral_linearIsometryEquiv_comp]
    | succ j ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, ih]
      funext t
      rw [Function.comp_apply,
        (hasFDerivAt_integral_pIter hK hKm hμK hΦ hc j t).fderiv,
        integral_linearIsometryEquiv_comp]
      simp
  refine ⟨key, ?_⟩
  apply contDiff_of_differentiable_iteratedFDeriv
  intro i _
  rw [key i]
  intro t
  exact (hasFDerivAt_integral_pIter hK hKm hμK hΦ hc i t).differentiableAt
end Formalism.IndefR.Tow.SobPf.Avg
