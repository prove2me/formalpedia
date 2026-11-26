-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.exp_sub_one_div_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:24.107931+00:00
-- url     : https://prove2.me/submissions/3f0fe49f-30ec-4794-8c4f-dd94309d100b

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
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
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (Real.exp x - 1) / x < (Real.exp y - 1) / y := by
  have hy : 0 < y := hx.trans hxy
  simpa using
    strictConvexOn_exp.secant_strict_mono
      (show (0 : ℝ) ∈ Set.univ by simp)
      (show x ∈ Set.univ by simp)
      (show y ∈ Set.univ by simp)
      hx.ne' hy.ne' hxy
end CollatzEndpointTransport.FixedTotal
