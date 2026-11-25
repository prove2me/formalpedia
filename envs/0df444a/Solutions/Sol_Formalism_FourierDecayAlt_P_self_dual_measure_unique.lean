-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.self_dual_measure_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:50:07.238072+00:00
-- url     : https://prove2.me/submissions/6e22491e-8ebd-436c-a786-f1ac1b70b6a9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_double_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G3_exists_schwartz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SelfDualUnique := by
  intro β hβ κ h
  obtain ⟨f, hf⟩ := exists_schwartz
  have h0 := h f 0
  rw [double_smul β hβ, neg_zero, hf, mul_one] at h0
  have hc : 0 < ‖β‖ / (2 * Real.pi) := by
    have := norm_pos_iff.mpr hβ
    positivity
  have h1 : (κ : ℝ) ^ 2 * ((‖β‖ / (2 * Real.pi)) ^ 2)⁻¹ = 1 := by exact_mod_cast h0
  have h2 : (κ : ℝ) ^ 2 = (‖β‖ / (2 * Real.pi)) ^ 2 := by
    field_simp at h1
    field_simp
    linarith
  have h3 : (κ : ℝ) = ‖β‖ / (2 * Real.pi) := by
    exact (pow_left_inj₀ κ.coe_nonneg hc.le two_ne_zero).mp h2
  rw [← h3, Real.toNNReal_coe]
end Formalism.FourierDecayAlt.P
