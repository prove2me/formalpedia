-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.log_sq_le_four_mul_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:34.761542+00:00
-- url     : https://prove2.me/submissions/8ae2a2f8-e152-44f0-a88c-53d59de7ef95

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_LfunctionOneLowerBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution {y : ℝ} (hy : 1 ≤ y) : Real.log y ^ 2 ≤ 4 * y := by
  have hy0 : 0 < y := by linarith
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hge : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have h1 : Real.log y = 2 * Real.log (Real.sqrt y) := by
    conv_lhs => rw [← Real.mul_self_sqrt hy0.le]
    rw [Real.log_mul hs.ne' hs.ne']; ring
  have h2 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 := Real.log_le_sub_one_of_pos hs
  have h0 : 0 ≤ Real.log (Real.sqrt y) := Real.log_nonneg hge
  have hsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  rw [h1]; nlinarith
end Formalism.HermitianLattices.Ext.SupplyAP
