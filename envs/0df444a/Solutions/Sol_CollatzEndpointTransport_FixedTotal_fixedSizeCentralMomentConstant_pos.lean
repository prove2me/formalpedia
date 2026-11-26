-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSizeCentralMomentConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:06:16.39162+00:00
-- url     : https://prove2.me/submissions/cf778ab7-3b76-4010-9ad0-5c0b7c0323be

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_lt_alpha
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_pos
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < fixedSizeCentralMomentConstant theta eta := by
  have hstar0 : 0 < centralRenyiPiStar theta eta :=
    centralRenyiPiStar_pos htheta0 htheta1 heta0 heta1
  have hstarAlpha : centralRenyiPiStar theta eta <
      centralRenyiAlpha theta :=
    centralRenyiPiStar_lt_alpha heta1
  have hgap := centralRenyiAlpha_den_pos htheta0
  have hden : 0 < (2 : ℝ) ^ theta - 1 -
      centralRenyiPiStar theta eta * ((3 : ℝ) ^ theta - 1) := by
    have hscaled :
        centralRenyiPiStar theta eta * ((3 : ℝ) ^ theta - 1) <
          (2 : ℝ) ^ theta - 1 := by
      unfold centralRenyiAlpha at hstarAlpha
      simpa [mul_comm] using (lt_div_iff₀ hgap).mp hstarAlpha
    linarith
  unfold fixedSizeCentralMomentConstant
  exact mul_pos (by norm_num)
    (add_pos_of_pos_of_nonneg (div_pos hstar0 hden) (by norm_num))
end CollatzEndpointTransport.FixedTotal
