-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_norm_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:51.808213+00:00
-- url     : https://prove2.me/submissions/90184a95-f21b-4fe0-ac7d-8ce99c345d5d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (E1 E0 a1 b1 a0 b0 V1 V0 : ℂ) :
    ‖(E1 + I * (a1 - b1) + V1) - (E0 + I * (a0 - b0) + V0)‖ ≤
      ‖E1‖ + ‖E0‖ + ‖a1‖ + ‖b1‖ + ‖a0‖ + ‖b0‖ + ‖V1 - V0‖ := by
  have e : (E1 + I * (a1 - b1) + V1) - (E0 + I * (a0 - b0) + V0) =
      E1 - E0 + I * a1 - I * b1 - I * a0 + I * b0 + (V1 - V0) := by ring
  rw [e]
  have h1 := norm_add_le (E1 - E0 + I * a1 - I * b1 - I * a0 + I * b0) (V1 - V0)
  have h2 := norm_add_le (E1 - E0 + I * a1 - I * b1 - I * a0) (I * b0)
  have h3 := norm_sub_le (E1 - E0 + I * a1 - I * b1) (I * a0)
  have h4 := norm_sub_le (E1 - E0 + I * a1) (I * b1)
  have h5 := norm_add_le (E1 - E0) (I * a1)
  have h6 := norm_sub_le E1 E0
  simp only [norm_mul, Complex.norm_I, one_mul] at h2 h3 h4 h5
  linarith
end Formalism.HermitianLattices.Ext.BoxTail
