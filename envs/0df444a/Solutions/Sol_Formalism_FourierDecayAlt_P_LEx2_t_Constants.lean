-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.t_Constants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:32:51.836308+00:00
-- url     : https://prove2.me/submissions/b44bbc6d-4787-4331-8122-e8bff9911181

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : Constants := by
  intro k r N C₂ C₆ I hr hC h6 hI
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrN : (r:ℝ) + 1 ≤ N := by exact_mod_cast hr
  have hq : (0:ℝ) ≤ ((r:ℝ)+1)^2 := by positivity
  have hA : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ)+1)^2 := by positivity
  have hB : (0:ℝ) ≤ (N:ℝ)^2 * ((r:ℝ)+1)^2 := by positivity
  have hC6 : C₂ ≤ C₆ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (k:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (le_trans hC.le hC6) hB]
  · push_cast
    have e : ((k:ℝ) + 2 * r + 1) * (C₂ * N * ((r:ℝ)+1)^2)
        = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) + C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) := by ring
    rw [e]
    have h2 : (2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2 ≤ 2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2) := by
      have : (2 * (r:ℝ) + 1) * N ≤ 2 * (N:ℝ)^2 := by nlinarith
      nlinarith
    have h3 : C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) ≤ C₂ * (2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2)) :=
      mul_le_mul_of_nonneg_left h2 hC.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg hC.le hB]
  · have : 6 * (N:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = 6 * C₂ * ((N:ℝ)^2 * ((r:ℝ)+1)^2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg (le_trans hC.le hC6) hA]
end Formalism.FourierDecayAlt.P.LEx2
