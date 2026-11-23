-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sP_cN_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:35.452615+00:00
-- url     : https://prove2.me/submissions/560a6f16-de61-4f0d-8d39-b2bd3ab8f352

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB

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
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ sP (cN x) N p := by
  unfold sP cN
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
