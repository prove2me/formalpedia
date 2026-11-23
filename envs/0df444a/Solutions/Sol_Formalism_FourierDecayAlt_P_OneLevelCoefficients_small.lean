-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:33.634646+00:00
-- url     : https://prove2.me/submissions/e37612f5-0919-4fe7-a354-c2a55b6dd6e5

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution (r f : ℕ) (C C₀ Θ : ℝ) (hΘ : 0 < Θ) (h0 : 0 ≤ C₀) (h : C₀ ≤ C)
    (hs : (r : ℝ) * (C / Θ) ^ f ≤ 1) : (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)) hs
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right h hΘ.le) f
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
