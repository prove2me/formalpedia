-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.b_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:25.591797+00:00
-- url     : https://prove2.me/submissions/db57189a-3a06-442e-a5fb-2892c606d92f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_b_root_sep
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_gradSmall6


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (z : ℂ) (hz : 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖)
    (x : Fin (m + 1) → ℂ) (hx : ∀ k, ‖x k - z‖ ≤ 2 * δ) (hx0 : ∀ k, x k ≠ 0) (k : Fin (m + 1)) :
    ‖x k - z‖ ≤ 6 * ‖z‖ * ‖dg0 (z ^ (m + 2)) x‖ := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hz0 : z ≠ 0 := norm_pos_iff.1 hzpos
  have hD : z ^ (m + 2) ≠ 0 := pow_ne_zero _ hz0
  have hδz : 2 * δ ≤ ‖z‖ / (50 * ((m : ℝ) + 2)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  obtain ⟨η₀, hη₀⟩ : ∃ η₀, η₀ = ‖dg0 (z ^ (m + 2)) x‖ := ⟨_, rfl⟩
  rw [← hη₀]
  have hη₀0 : 0 ≤ η₀ := hη₀ ▸ norm_nonneg _
  rcases le_or_gt (1 / (16 * ((m : ℝ) + 2))) η₀ with hbig | hsmall
  · calc ‖x k - z‖ ≤ ‖z‖ / (50 * ((m : ℝ) + 2)) := (hx k).trans hδz
      _ ≤ 6 * ‖z‖ * (1 / (16 * ((m : ℝ) + 2))) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        norm_num
      _ ≤ 6 * ‖z‖ * η₀ := by gcongr
  · refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨d, hd⟩ : ∃ d, d = min (e / (6 * ‖z‖)) (1 / (16 * ((m : ℝ) + 2))) := ⟨_, rfl⟩
    have hd0 : 0 < d := by rw [hd]; exact lt_min (by positivity) (by positivity)
    have hd1 : d ≤ e / (6 * ‖z‖) := hd ▸ min_le_left _ _
    have hd2 : d ≤ 1 / (16 * ((m : ℝ) + 2)) := hd ▸ min_le_right _ _
    have h8 : η₀ + d ≤ 1 / (8 * ((m : ℝ) + 2)) := by
      have : 1 / (8 * ((m : ℝ) + 2)) = 1 / (16 * ((m : ℝ) + 2)) + 1 / (16 * ((m : ℝ) + 2)) := by
        field_simp; norm_num
      linarith
    have h4 : η₀ + d ≤ 1 / (4 * ((m : ℝ) + 2)) := by
      refine h8.trans ?_
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    obtain ⟨z', hz', hxz'⟩ := G1.gradSmall6 m _ hD x hx0 (η₀ + d) (by linarith) h4
      (fun k => lt_of_le_of_lt (hη₀ ▸ norm_le_pi_norm _ k) (by linarith))
    have hnz' : ‖z'‖ = ‖z‖ := by
      have : ‖z'‖ ^ (m + 2) = ‖z‖ ^ (m + 2) := by rw [← norm_pow, hz', norm_pow]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by omega)).1 this
    have hzz : z' = z := by
      by_contra hne
      have hsep := b_root_sep (m + 2) (by omega) z z' hz0 hz' hne
      have h5 : ‖z' - z‖ ≤ ‖x k - z‖ + ‖x k - z'‖ := by
        have : z' - z = (x k - z) - (x k - z') := by ring
        rw [this]; exact norm_sub_le _ _
      have h6 := hxz' k
      rw [hnz'] at h6
      have h7 : 6 * (η₀ + d) * ‖z‖ ≤ 6 * (1 / (8 * ((m : ℝ) + 2))) * ‖z‖ := by gcongr
      have h9 : ‖z' - z‖ ≤ ‖z‖ / (50 * ((m : ℝ) + 2)) + 6 * (1 / (8 * ((m : ℝ) + 2))) * ‖z‖ := by
        linarith [hx k]
      have h10 : ((m + 2 : ℕ) : ℝ) * (‖z‖ / (50 * ((m : ℝ) + 2)) + 6 * (1 / (8 * ((m : ℝ) + 2))) * ‖z‖)
          = (77 / 100) * ‖z‖ := by
        push_cast
        field_simp
        norm_num
      have h11 : ((m + 2 : ℕ) : ℝ) * ‖z' - z‖ ≤ (77 / 100) * ‖z‖ := by
        rw [← h10]
        exact mul_le_mul_of_nonneg_left h9 (Nat.cast_nonneg _)
      linarith
    have h6 := hxz' k
    rw [hzz] at h6
    have h12 : 6 * d * ‖z‖ ≤ e := by
      have := mul_le_mul_of_nonneg_right hd1 (by positivity : (0 : ℝ) ≤ 6 * ‖z‖)
      rw [div_mul_cancel₀ _ (by positivity)] at this
      linarith
    linarith
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
