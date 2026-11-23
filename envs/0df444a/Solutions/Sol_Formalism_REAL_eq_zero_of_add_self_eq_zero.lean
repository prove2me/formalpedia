-- Prove2me | solution 1 for Formalism.REAL.eq_zero_of_add_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:10.474807+00:00
-- url     : https://prove2.me/submissions/7133b98c-4378-435d-bd83-3cb01847ad9e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (h : X + X = 0) : X = 0 := by
  calc X = ((2 : ℂ)⁻¹ * 2) • X := by rw [inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = (2 : ℂ)⁻¹ • (X + X) := by rw [mul_smul, two_smul]
    _ = 0 := by rw [h, smul_zero]
end Formalism.REAL
