-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.J_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:01.815948+00:00
-- url     : https://prove2.me/submissions/c5fe2a4c-12d3-44ec-b065-49d2f4b0de54

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue
import Theorems.Thm_Formalism_FourierDecayAlt_P_DiscFubiniVolume_J_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution {u : ℝ} (hu : 0 < u) :
    ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 10 / (u * Real.sqrt u) := by
  rcases le_or_gt 1 u with h | h
  · exact J_bound h
  · have hb : ‖∫ t in (-1 : ℝ)..1, (g0 t : ℂ) * ee u t‖ ≤ 1 * |1 - (-1 : ℝ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      rw [norm_mul]
      have h1 : ‖(g0 t : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, show g0 t = Real.sqrt (1 - t ^ 2) from rfl,
          abs_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (1 - t ^ 2) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
          _ = 1 := Real.sqrt_one
      have h2 : ‖ee u t‖ = 1 := by
        simp only [ee]
        exact Complex.norm_exp_I_mul_ofReal _
      rw [h2, mul_one]
      exact h1
    have hsu : Real.sqrt u ≤ 1 := by
      calc Real.sqrt u ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h.le
        _ = 1 := Real.sqrt_one
    have hpos : 0 < u * Real.sqrt u := mul_pos hu (Real.sqrt_pos.mpr hu)
    have hle : u * Real.sqrt u ≤ 1 := by nlinarith [Real.sqrt_nonneg u]
    have h10 : 2 ≤ 10 / (u * Real.sqrt u) := by
      rw [le_div_iff₀ hpos]
      linarith
    have e2 : (1 : ℝ) * |1 - (-1 : ℝ)| = 2 := by norm_num
    linarith
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
