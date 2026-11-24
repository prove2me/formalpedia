-- Prove2me | solution 1 for Formalism.H.poisson_periodization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:05.427337+00:00
-- url     : https://prove2.me/submissions/ed034e12-a8b3-4de5-ad37-e3815b228314

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Periodization
import Theorems.Thm_Formalism_H_PoissonPeriodization_exists_global_bound
import Theorems.Thm_Formalism_H_PoissonPeriodization_shift_bound
import Theorems.Thm_Formalism_H_PoissonPeriodization_summable_one_add_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
open PoissonPeriodization
namespace Formalism.H
theorem _root_.solution (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : Periodization V := by
  unfold Periodization
  intro Λ _ _ f hf b hb hO
  have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg _) hb.le
  obtain ⟨C, hC0, hC⟩ := exists_global_bound hf hb0 hO
  have hS := summable_one_add_norm Λ hb
  have hbound : ∀ (R : ℝ), 0 ≤ R → ∀ (l : Λ) (x : V), ‖x‖ ≤ R →
      ‖f (↑l + x)‖ ≤ C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by
    intro R hR l x hx
    calc ‖f (↑l + x)‖ ≤ C * (1 + ‖(l : V) + x‖) ^ (-b) := hC _
      _ ≤ C * ((1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b)) :=
          mul_le_mul_of_nonneg_left (shift_bound hb0 hR (l : V) x hx) hC0
      _ = C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((integrable_one_add_norm hb).const_mul C).mono' hf.aestronglyMeasurable ?_
    exact ae_of_all _ (fun v => hC v)
  · intro x
    first
      | exact Summable.of_norm_bounded (hS.mul_left (C * (1 + ‖x‖) ^ b))
          (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
      | exact Summable.of_norm_bounded _ (hS.mul_left (C * (1 + ‖x‖) ^ b))
          (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
  · refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
    have hcont : ContinuousOn (fun x => ∑' l : Λ, f (↑l + x)) (Metric.ball (0 : V) (‖x₀‖ + 1)) := by
      refine continuousOn_tsum (fun l => (hf.comp (continuous_const.add continuous_id)).continuousOn)
        (hS.mul_left (C * (1 + (‖x₀‖ + 1)) ^ b)) ?_
      intro l x hx
      exact hbound (‖x₀‖ + 1) (by positivity) l x (by simpa using (Metric.mem_ball.mp hx).le)
    exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
  · intro l₀ x
    have h := (Equiv.addRight l₀).tsum_eq (fun l : Λ => f (↑l + x))
    simp only [Equiv.coe_addRight, Submodule.coe_add, add_assoc] at h
    exact h
end Formalism.H
