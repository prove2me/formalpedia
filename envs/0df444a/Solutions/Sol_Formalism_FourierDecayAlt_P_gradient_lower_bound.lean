-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gradient_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:56.086135+00:00
-- url     : https://prove2.me/submissions/3fc67b00-0896-4c7f-aa4a-70c67668db32

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.GradLower := by
  intro m Kc hK h0 δ hδ
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hR1 : (1 : ℝ) ≤ max 1 R := le_max_left _ _
  have hc1 : (0 : ℝ) < 1 / (4 * ((m : ℝ) + 2)) := by positivity
  have hc2 : (0 : ℝ) < δ / (12 * max 1 R) := by positivity
  refine ⟨min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)), lt_min hc1 hc2, ?_⟩
  intro D' hD x hx hfar
  by_contra hcon
  push Not at hcon
  have hD0 : D' ≠ 0 := fun h => h0 (h ▸ hD)
  obtain ⟨z, hz, hzx⟩ := gradSmall6 m D' hD0 x hx _ (lt_min hc1 hc2) (min_le_left _ _) hcon
  have hzn : ‖z‖ ≤ max 1 R := by
    by_contra hlt
    push Not at hlt
    have h1 : 1 ≤ ‖z‖ := hR1.trans hlt.le
    have h2 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ h1 (by omega)
    rw [← norm_pow, hz] at h2
    have h3 := hR D' hD
    have h4 : R ≤ max 1 R := le_max_right _ _
    linarith
  have hle : ‖x - fun _ => z‖ ≤ δ / 2 := by
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro k
    simp only [Pi.sub_apply]
    refine (hzx k).trans ?_
    have h5 : min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) ≤ δ / (12 * max 1 R) := min_le_right _ _
    have h6 : 0 < min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) := lt_min hc1 hc2
    calc 6 * min (1 / (4 * ((m : ℝ) + 2))) (δ / (12 * max 1 R)) * ‖z‖
        ≤ 6 * (δ / (12 * max 1 R)) * max 1 R := by
          apply mul_le_mul _ hzn (norm_nonneg _) (by positivity)
          linarith
      _ = δ / 2 := by field_simp; norm_num
  have := hfar z hz
  linarith
end Formalism.FourierDecayAlt.P
