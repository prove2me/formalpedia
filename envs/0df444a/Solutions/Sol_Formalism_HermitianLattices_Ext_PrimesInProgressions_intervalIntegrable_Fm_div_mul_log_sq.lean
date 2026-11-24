-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.intervalIntegrable_Fm_div_mul_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:09.553942+00:00
-- url     : https://prove2.me/submissions/7090936a-5e72-409d-b1f7-adf7d2c31f5e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_continuousOn_Fm_div_mul_log_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Fm K θ β t / (t * Real.log t ^ 2)) MeasureTheory.volume a b := by
  exact (continuousOn_Fm_div_mul_log_sq K θ β ha).intervalIntegrable_of_Icc hab
end Formalism.HermitianLattices.Ext.PrimesInProgressions
