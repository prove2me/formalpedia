-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.continuousOn_Fm_div_mul_log_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:34.715891+00:00
-- url     : https://prove2.me/submissions/1077e1d8-69e8-4dee-96f4-bebffb20517e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB

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
theorem _root_.solution (K θ β : ℝ) {a b : ℝ} (ha : 2 ≤ a) :
    ContinuousOn (fun t => Fm K θ β t / (t * Real.log t ^ 2)) (Set.Icc a b) := by
  have hpos : ∀ t ∈ Set.Icc a b, 2 ≤ t := fun t ht => le_trans ha ht.1
  apply ContinuousOn.div
  · unfold Fm
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.sub continuousOn_id
    apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact ContinuousOn.rpow_const continuousOn_id (fun t ht => Or.inl (by simp; linarith [hpos t ht]))
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.pow
    exact Real.continuousOn_log.mono (fun t ht => by simp; linarith [hpos t ht])
  · intro t ht
    have h2 := hpos t ht
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 (Real.log_pos (by linarith)).ne')
end Formalism.HermitianLattices.Ext.PrimesInProgressions
