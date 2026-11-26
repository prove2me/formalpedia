-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:40.207538+00:00
-- url     : https://prove2.me/submissions/4ec446f8-2e99-4984-9ddf-2ed2c7148b24

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ}
    (htheta : 0 < theta) (hpi : 0 < pi)
    (hpialpha : pi < centralRenyiAlpha theta) :
    centralRenyiRatio theta pi < 1 := by
  have hden := centralRenyiRatio_den_pos htheta hpi
  have hthree : 0 < (3 : ℝ) ^ theta - 1 :=
    centralRenyiAlpha_den_pos htheta
  have hscaled :
      ((3 : ℝ) ^ theta - 1) * pi < (2 : ℝ) ^ theta - 1 := by
    unfold centralRenyiAlpha at hpialpha
    simpa [mul_comm] using (lt_div_iff₀ hthree).mp hpialpha
  unfold centralRenyiRatio
  rw [div_lt_one hden]
  linarith
end CollatzEndpointTransport.FixedTotal
