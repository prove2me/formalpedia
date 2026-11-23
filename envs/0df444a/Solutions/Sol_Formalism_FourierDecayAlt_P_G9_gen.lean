-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:57.650439+00:00
-- url     : https://prove2.me/submissions/46cabfd6-524f-4aa0-bd67-5a82504de5f9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_integral_comp_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_G9_exists_rot

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
theorem _root_.solution (δ : ℝ) (γ : ℂ) (hδ : 0 < δ) :
    ∫ w : ℂ, ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (((γ * w ^ 2).re : ℝ) : ℂ)) =
      ((Real.pi / Real.sqrt (δ ^ 2 + ‖γ‖ ^ 2) : ℝ) : ℂ) := by
  obtain ⟨u, hu, hγ⟩ := exists_rot γ
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h := integral_comp_mul u hu0 (fun w : ℂ => ((Real.exp (-δ * ‖w‖ ^ 2) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (((γ * w ^ 2).re : ℝ) : ℂ)))
  rw [hu] at h
  simp only [one_pow, inv_one, one_smul] at h
  rw [← h, ← core δ ‖γ‖ hδ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  have e : γ * (u * w) ^ 2 = (‖γ‖ : ℂ) * w ^ 2 := by rw [← hγ]; ring
  rw [e, norm_mul, hu, one_mul, Complex.re_ofReal_mul]
end Formalism.FourierDecayAlt.P.G9
