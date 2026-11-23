-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G9.exists_rot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:09.62132+00:00
-- url     : https://prove2.me/submissions/7230a7e7-cd47-47dd-9343-57befcc64527

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral

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
theorem _root_.solution (γ : ℂ) : ∃ u : ℂ, ‖u‖ = 1 ∧ γ * u ^ 2 = (‖γ‖ : ℂ) := by
  refine ⟨Complex.exp (-(γ.arg / 2 : ℝ) * Complex.I), ?_, ?_⟩
  · have : (-((γ.arg / 2 : ℝ) : ℂ) * Complex.I) = ((-(γ.arg / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  · have h0 := Complex.norm_mul_exp_arg_mul_I γ
    generalize γ.arg = θ at h0 ⊢
    rw [← h0, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    have : (θ : ℂ) * Complex.I + ((2 : ℕ) : ℂ) * (-((θ / 2 : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast; ring
    rw [this, Complex.exp_zero, mul_one, h0]
end Formalism.FourierDecayAlt.P.G9
