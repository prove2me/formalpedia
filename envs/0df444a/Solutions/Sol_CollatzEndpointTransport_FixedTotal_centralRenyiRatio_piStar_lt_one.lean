-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiRatio_piStar_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:00.937615+00:00
-- url     : https://prove2.me/submissions/bcc44d26-940d-45ca-8b44-ec58b093817c

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_lt_alpha
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPiStar_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralRenyiRatio theta (centralRenyiPiStar theta eta) < 1 := by
  exact centralRenyiRatio_lt_one htheta0
    (centralRenyiPiStar_pos htheta0 htheta1 heta0 heta1)
    (centralRenyiPiStar_lt_alpha heta1)
end CollatzEndpointTransport.FixedTotal
