-- Prove2me | solution 1 for FriedCrossing.ParamInt.contDiff_parametric_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:33.894989+00:00
-- url     : https://prove2.me/submissions/521b052e-e845-484b-8d7f-e3191412ba9a

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Definitions.Def_B1s_cluster_from_resolvent_9_11
import Theorems.Thm_FriedCrossing_ParamInt_contDiff_uncurry_partialX
import Theorems.Thm_FriedCrossing_ParamInt_hasFDerivAt_partialX

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
open FriedCrossing.ParamInt
namespace FriedCrossing.ParamInt
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (a b : ℝ) :
    ∀ (n : ℕ) (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (F : E → ℝ → G), ContDiff ℝ n (Function.uncurry F) →
      ContDiff ℝ n fun x => ∫ t in a..b, F x t := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ F hF
    simp only [Nat.cast_zero, contDiff_zero] at hF ⊢
    exact continuous_parametric_intervalIntegral_of_continuous' hF a b
  | succ n ih =>
    intro G _ _ _ F hF
    have hcont : Continuous (Function.uncurry F) := hF.continuous
    have hF' := contDiff_uncurry_partialX F n hF
    have hF'cont : Continuous (Function.uncurry (partialX F)) := hF'.continuous
    -- differentiability at every x₀, with derivative ∫ ∂ₓF
    have hd : ∀ x₀ : E, HasFDerivAt (fun x => ∫ t in a..b, F x t)
        (∫ t in a..b, partialX F x₀ t) x₀ := by
      intro x₀
      -- a bound on ‖∂ₓF‖ over the compact set closedBall x₀ 1 × uIcc a b
      have hK : IsCompact (Metric.closedBall x₀ 1 ×ˢ Set.uIcc a b) :=
        (isCompact_closedBall x₀ 1).prod isCompact_uIcc
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'cont.continuousOn
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (bound := fun _ => C)
        (s := Metric.ball x₀ 1) (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun x =>
          (hcont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      · exact (hcont.comp (Continuous.prodMk continuous_const continuous_id)).intervalIntegrable a b
      · exact (hF'cont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      · refine Eventually.of_forall fun t ht x hx => ?_
        exact hC (x, t) ⟨Metric.ball_subset_closedBall hx, Set.uIoc_subset_uIcc ht⟩
      · exact intervalIntegrable_const
      · exact Eventually.of_forall fun t _ x _ => hasFDerivAt_partialX F n hF x t
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hd x).differentiableAt, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
    have hfd : fderiv ℝ (fun x => ∫ t in a..b, F x t) = fun x => ∫ t in a..b, partialX F x t := by
      funext x; exact (hd x).fderiv
    rw [hfd]
    exact ih (E →L[ℝ] G) (partialX F) hF'
end FriedCrossing.ParamInt
