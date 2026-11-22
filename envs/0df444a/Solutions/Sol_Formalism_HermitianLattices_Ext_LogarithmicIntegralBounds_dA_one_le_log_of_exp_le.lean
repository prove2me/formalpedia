-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_one_le_log_of_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:26.482858+00:00
-- url     : https://prove2.me/submissions/073e0621-ddcf-4f46-8e1e-5be96f7dc600

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA

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
open ArithmeticFunction (vonMangoldt)
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hx
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
