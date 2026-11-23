-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.gaussOneDamped
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:21.26383+00:00
-- url     : https://prove2.me/submissions/6e45088e-04bb-4bf0-9c8b-4be75e6093f9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G9
namespace Formalism.FourierDecayAlt.P.G9
theorem _root_.solution : Formalism.FourierDecayAlt.G.GaussOneDamped := by
  intro β a δ hδ
  have hc : 0 ≤ ‖β‖ / (2 * Real.pi) := by positivity
  unfold mu psi
  rw [integral_smul_nnreal_measure]
  have e : ∀ w : ℂ, β * (a * w ^ 2 / 2) = (β * a / 2) * w ^ 2 := fun w => by ring
  simp_rw [e]
  rw [gen δ (β * a / 2) hδ]
  rw [NNReal.smul_def, Real.coe_toNNReal _ hc, Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  have h1 : 4 * δ ^ 2 + ‖β‖ ^ 2 * ‖a‖ ^ 2 = 2 ^ 2 * (δ ^ 2 + ‖β * a / 2‖ ^ 2) := by
    rw [norm_div, norm_mul]; simp; ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have h2 : 0 < Real.sqrt (δ ^ 2 + ‖β * a / 2‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have := Real.pi_pos
  field_simp
end Formalism.FourierDecayAlt.P.G9
