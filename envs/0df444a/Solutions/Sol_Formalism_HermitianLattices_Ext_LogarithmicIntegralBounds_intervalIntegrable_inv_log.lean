-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.intervalIntegrable_inv_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:18.690222+00:00
-- url     : https://prove2.me/submissions/10ed6ed5-501d-4b52-83cf-fdbfa32b0d2f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h
    · linarith [h.1]
    · linarith [h.1]
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    have h2 := hmem t ht
    exact ne_of_gt (by linarith)
  · intro t ht
    have h2 := hmem t ht
    exact (Real.log_pos (by linarith)).ne'
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
