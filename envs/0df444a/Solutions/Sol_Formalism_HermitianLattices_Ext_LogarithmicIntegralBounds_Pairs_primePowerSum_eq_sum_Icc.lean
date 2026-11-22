-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.primePowerSum_eq_sum_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:24.101946+00:00
-- url     : https://prove2.me/submissions/0062c5c2-d31a-4b16-a673-efc8e8688390

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
theorem _root_.solution (c : ℕ → ℝ) (N p : ℕ) : sP c N p = ∑ n ∈ Icc 1 N, aW c p n := by
  simp only [sP, aW, Finset.sum_filter]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
