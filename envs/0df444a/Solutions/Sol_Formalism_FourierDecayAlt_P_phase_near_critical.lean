-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_near_critical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:52.984695+00:00
-- url     : https://prove2.me/submissions/a87cbe72-3bf9-4962-893e-ec356db72719

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_b_differentiableAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_b_near

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.PhaseFunctionNearCritical := by
  intro m δ Rz hδ
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨(2 * ((m : ℝ) + 1) + 2 ^ (m + 1) + 6) * |Rz| + 1, by positivity, ?_⟩
  intro z hz hzR
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hzR' : ‖z‖ ≤ |Rz| := hzR.trans (le_abs_self _)
  have hδz : 4 * δ ≤ ‖z‖ / 2 := by nlinarith
  have hball : ∀ x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)), ∀ k,
      ‖z‖ / 2 ≤ ‖x k‖ ∧ ‖x k‖ ≤ 2 * ‖z‖ := by
    intro x hx k
    rw [mem_ball_iff_norm] at hx
    have h1 : ‖x k - z‖ ≤ ‖x - fun _ => z‖ := norm_le_pi_norm (x - fun _ => z) k
    have h2 : ‖z‖ - ‖x k - z‖ ≤ ‖x k‖ := by
      have : ‖z‖ ≤ ‖x k‖ + ‖x k - z‖ := by
        have e : z = x k - (x k - z) := by ring
        calc ‖z‖ = ‖x k - (x k - z)‖ := by rw [← e]
          _ ≤ _ := norm_sub_le _ _
      linarith
    have h3 : ‖x k‖ ≤ ‖z‖ + ‖x k - z‖ := by
      have e : x k = z + (x k - z) := by ring
      calc ‖x k‖ = ‖z + (x k - z)‖ := by rw [← e]
        _ ≤ _ := norm_add_le _ _
    constructor <;> linarith
  have hne : ∀ x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)), ∀ k, x k ≠ 0 := by
    intro x hx k
    have := (hball x hx k).1
    exact norm_pos_iff.1 (by linarith)
  refine ⟨fun x hx => ⟨hne x hx, ?_⟩, fun x hx => (PhaseFunctionDerivatives.b_differentiableAt _ x (hne x hx)).differentiableWithinAt,
    ?_⟩
  · unfold g0
    have h1 : ‖∑ k, x k‖ ≤ 2 * ((m : ℝ) + 1) * ‖z‖ := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => (hball x hx k).2).trans ?_
      simp
      linarith
    have h2 : (‖z‖ / 2) ^ (m + 1) ≤ ‖∏ k, x k‖ := by
      rw [norm_prod]
      have := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin (m + 1) => ‖z‖ / 2)
        (g := fun k => ‖x k‖) (fun _ _ => by positivity) (fun k _ => (hball x hx k).1)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have h3 : ‖z ^ (m + 2) / ∏ k, x k‖ ≤ 2 ^ (m + 1) * ‖z‖ := by
      rw [norm_div, norm_pow, div_le_iff₀ (lt_of_lt_of_le (by positivity) h2)]
      calc ‖z‖ ^ (m + 2) = 2 ^ (m + 1) * ‖z‖ * (‖z‖ / 2) ^ (m + 1) := by
            rw [div_pow]; field_simp; ring
        _ ≤ _ := by gcongr
    refine (norm_add_le _ _).trans ?_
    have h4 : (2 * ((m : ℝ) + 1) + 2 ^ (m + 1) + 6) * ‖z‖ ≤ (2 * ((m : ℝ) + 1) + 2 ^ (m + 1) + 6) * |Rz| := by
      gcongr
    nlinarith
  · intro x hx
    have hx' : x ∈ Metric.ball (fun _ : Fin (m + 1) => z) (2 * (2 * δ)) :=
      Metric.closedBall_subset_ball (by linarith) hx
    rw [mem_closedBall_iff_norm] at hx
    have hxk : ∀ k, ‖x k - z‖ ≤ 2 * δ := fun k => (norm_le_pi_norm (x - fun _ => z) k).trans hx
    have hd0 : 0 ≤ ‖dg0 (z ^ (m + 2)) x‖ := norm_nonneg _
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    refine (PhaseFunctionDerivatives.b_near m δ hδ z hz x hxk (hne x hx') k).trans ?_
    apply mul_le_mul_of_nonneg_right _ hd0
    have : (0 : ℝ) ≤ 2 ^ (m + 1) := by positivity
    have h0 : 0 ≤ |Rz| := abs_nonneg _
    nlinarith
end Formalism.FourierDecayAlt.P
