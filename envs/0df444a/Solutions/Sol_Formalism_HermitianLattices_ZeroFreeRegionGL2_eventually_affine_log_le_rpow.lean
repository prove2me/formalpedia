-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.eventually_affine_log_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:50:50.003596+00:00
-- url     : https://prove2.me/submissions/e4dec16b-9938-47c1-8c63-d61338904a45

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_mul_log_le_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution (a P Q s : ℝ) (ha : 0 < a) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, P + Q * Real.log x ≤ s * x ^ a := by
  filter_upwards [eventually_le_rpow a (2 * (P / s)) ha, eventually_mul_log_le_rpow a (2 * (Q / s)) ha] with x h1 h2
  have h3 : P / s + Q / s * Real.log x ≤ x ^ a := by linarith
  calc P + Q * Real.log x = s * (P / s + Q / s * Real.log x) := by field_simp
    _ ≤ s * x ^ a := mul_le_mul_of_nonneg_left h3 hs.le
end Formalism.HermitianLattices.ZeroFreeRegionGL2
