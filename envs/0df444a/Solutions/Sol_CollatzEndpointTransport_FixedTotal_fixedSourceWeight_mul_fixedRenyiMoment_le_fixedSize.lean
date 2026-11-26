-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSourceWeight_mul_fixedRenyiMoment_le_fixedSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:27.120491+00:00
-- url     : https://prove2.me/submissions/832b71f0-1fc4-450a-909d-d9bea371cccf

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_central_uniform_le_fixedSize
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSourceWeight_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_source_weight_scale_eq


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hcen : InCentralRenyiWindow N s eta)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
      fixedSizeCentralMomentConstant theta eta *
        (fixedSourceWeight N s) ^ (1 - theta) := by
  have hcard : 0 < (fixedSet N s).card := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact Nat.choose_pos (by omega)
  have hmoment := fixedRenyiMoment_central_uniform_le_fixedSize
    htheta0 htheta1 heta0 heta1 hN hs1 hsN hcen hsizePi hsizeDrift
  have hweight0 := fixedSourceWeight_nonneg N s
  calc
    fixedSourceWeight N s * fixedRenyiMoment N s theta ≤
        fixedSourceWeight N s *
          (fixedSizeCentralMomentConstant theta eta *
            ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta))) :=
      mul_le_mul_of_nonneg_left hmoment hweight0
    _ = fixedSizeCentralMomentConstant theta eta *
          (fixedSourceWeight N s *
            ((((2 : ℝ) ^ N) ^ theta) /
              (((fixedSet N s).card : ℝ) ^ theta))) := by ring
    _ = fixedSizeCentralMomentConstant theta eta *
          (fixedSourceWeight N s) ^ (1 - theta) := by
      rw [source_weight_scale_eq hcard htheta1]
end CollatzEndpointTransport.FixedTotal
