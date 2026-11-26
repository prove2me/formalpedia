-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapD_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:22:09.107878+00:00
-- url     : https://prove2.me/submissions/9d29b5ae-c247-4ec0-923a-768cc53499ab

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {chi Dc : ℝ}
    (hchi : 0 < chi) (hDc : 0 < Dc) (R : ℕ) :
    0 < bootstrapD chi Dc R := by
  unfold bootstrapD
  positivity
end FirstPassageLinearTransport
