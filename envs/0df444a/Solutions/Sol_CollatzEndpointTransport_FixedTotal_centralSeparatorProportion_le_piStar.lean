-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralSeparatorProportion_le_piStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:26.828207+00:00
-- url     : https://prove2.me/submissions/2f7416f7-9e13-4819-aaf8-d0be6ea17b60

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_window_upper

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta eta : ℝ}
    (hN : 1 < N) (hs : 0 < s)
    (hcen : InCentralRenyiWindow N s eta)
    (hsize :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1)) :
    centralSeparatorProportion N s ≤ centralRenyiPiStar theta eta := by
  have hNcast : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) - 1 := by linarith
  have hupper := central_window_upper hcen
  unfold centralRenyiGap at hsize
  unfold centralSeparatorProportion centralRenyiPiStar centralRenyiGap
  have hsCast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s)]
    norm_num
  have hNCast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hsCast, hNCast]
  rw [div_le_iff₀ hden]
  nlinarith
end CollatzEndpointTransport.FixedTotal
