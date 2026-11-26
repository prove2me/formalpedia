-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSourceWeight_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:36.569256+00:00
-- url     : https://prove2.me/submissions/2df40b3a-4bee-4fe4-80ee-c0634806d90f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSet_card_le_two_pow

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) :
    fixedSourceWeight N s ≤ 1 := by
  unfold fixedSourceWeight
  rw [div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ N)]
  exact_mod_cast fixedSet_card_le_two_pow N s
end CollatzEndpointTransport.FixedTotal
