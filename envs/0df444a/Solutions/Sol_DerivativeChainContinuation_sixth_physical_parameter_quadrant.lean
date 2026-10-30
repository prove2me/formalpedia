-- Prove2me | solution 1 for DerivativeChainContinuation.sixth_physical_parameter_quadrant
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:48:20.353052+00:00
-- url     : https://prove2.me/submissions/0df0a19f-f4c7-4bf4-ae21-acb28de83d44

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SixthPhysicalNormalization
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_sixth_physical_parameter_dictionary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate





theorem sixth_prefix_radius_positive : 0<sixthPrefixRadius := by
  unfold sixthPrefixRadius
  positivity







theorem sixth_physical_scale_positive : 0<sixthPhysicalScale := by
  unfold sixthPhysicalScale
  exact one_div_pos.mpr sixth_prefix_radius_positive















end DerivativeChainContinuation

theorem solution (β : ℂ) (hR : 0≤β.re) (hI : 0<β.im) :
    0≤(sixthPhysicalParameter β).re ∧ 0<(sixthPhysicalParameter β).im := by
  have hscale:=sixth_physical_scale_positive
  have he : sixthPhysicalParameter β=(((136*sixthPhysicalScale^3:ℝ):ℂ))*β := by
    rw [sixth_physical_parameter_dictionary]
    push_cast
    ring
  rw [he]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero]
  constructor <;> positivity
