-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.c_scale
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:20.014931+00:00
-- url     : https://prove2.me/submissions/3356ebe7-4f00-4333-beb3-6aa1bd0c0532

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution (a τ : ℝ) (ha : 1 ≤ a) (hτ : 1 ≤ τ) (E' : ℕ) (A : ℝ) :
    (1 + τ * a) ^ E' * (max 1 (τ * a)) ^ (-A) ≤
      τ ^ ((E' : ℝ) - A) * ((1 + a) ^ E' * (max 1 a) ^ (-A)) := by
  have hτ0 : 0 < τ := by linarith
  have ha0 : 0 < a := by linarith
  have h1 : 1 ≤ τ * a := by nlinarith
  rw [max_eq_right h1, max_eq_right ha, Real.mul_rpow hτ0.le ha0.le, Real.rpow_sub hτ0, Real.rpow_natCast,
    Real.rpow_neg hτ0.le]
  have h2 : (1 + τ * a) ^ E' ≤ (τ * (1 + a)) ^ E' := pow_le_pow_left₀ (by positivity) (by nlinarith) _
  rw [mul_pow] at h2
  have h3 : 0 ≤ (τ ^ A)⁻¹ * a ^ (-A) := by positivity
  calc (1 + τ * a) ^ E' * ((τ ^ A)⁻¹ * a ^ (-A))
      ≤ (τ ^ E' * (1 + a) ^ E') * ((τ ^ A)⁻¹ * a ^ (-A)) := mul_le_mul_of_nonneg_right h2 h3
    _ = _ := by rw [div_eq_mul_inv]; ring
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
