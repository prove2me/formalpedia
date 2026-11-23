-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.geomAlt_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.228843+00:00
-- url     : https://prove2.me/submissions/bf2c0a3d-4ba1-4cb3-830d-ed404afd9c07

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [Field K] [CharZero K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution : geometricSignedSeries K * (1 + X) = 1 := by
  ext n
  rw [mul_add, mul_one, map_add, mul_comm]
  rcases n with _ | m
  · simp [geometricSignedSeries]
  · rw [coeff_succ_X_mul]
    simp only [geometricSignedSeries, coeff_mk, coeff_one]
    rw [← map_add]
    have : ((-1 : ℚ) ^ (m + 1) + (-1) ^ m) = 0 := by ring
    simp [this]
end Formalism.ELL.PadicLogarithmSubstitution
