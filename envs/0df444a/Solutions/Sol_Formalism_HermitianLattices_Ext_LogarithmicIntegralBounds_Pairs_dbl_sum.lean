-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.dbl_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:24.071453+00:00
-- url     : https://prove2.me/submissions/e81a8beb-6339-431d-853d-230d291627b8

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
theorem _root_.solution (s : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ n ∈ s, ∑ n' ∈ s, f n * g n' = (∑ n ∈ s, f n) * ∑ n ∈ s, g n := by
  rw [Finset.sum_mul_sum]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
