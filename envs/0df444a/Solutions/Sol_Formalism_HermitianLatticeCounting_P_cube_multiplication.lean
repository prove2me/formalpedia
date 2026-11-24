-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cube_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:01:30.92053+00:00
-- url     : https://prove2.me/submissions/ffc3a208-e945-41b1-ad7b-92ce533f1c65

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_NearFarVolumeBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory NumberField
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : CubeMult := by
  intro C n f b₁ τ hC hb hτ
  have e1 : 4 / (1 / (C * n * b₁)) = 4 * (C * n * b₁) := by rw [one_div, div_inv_eq_mul]
  have s2 : Real.sqrt (n:ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  rw [e1, show 2 * n ^ 2 * f = 2 * (n ^ 2 * f) by ring, show 4 * n ^ 2 * f = 4 * (n ^ 2 * f) by ring,
    pow_mul (C * Real.sqrt n / τ ^ 2) 2, pow_mul (4 * C / τ) 4, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have e2 : (C * Real.sqrt n / τ ^ 2) ^ 2 = C ^ 2 * n / τ ^ 4 := by
    rw [div_pow, mul_pow, s2]; ring
  have e3 : (4 * C / τ) ^ 4 = 256 * C ^ 4 / τ ^ 4 := by rw [div_pow]; ring
  rw [e2, e3, mul_div_assoc', mul_div_assoc']
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hC2 : C ^ 2 ≤ 256 * C ^ 4 := by
    have : 1 ≤ C ^ 2 := by nlinarith
    nlinarith
  calc 4 * (C * n * b₁) * (C ^ 2 * n) = (4 * C * (n:ℝ) ^ 2 * b₁) * C ^ 2 := by ring
    _ ≤ (4 * C * (n:ℝ) ^ 2 * b₁) * (256 * C ^ 4) := by gcongr
end Formalism.HermitianLatticeCounting.P
