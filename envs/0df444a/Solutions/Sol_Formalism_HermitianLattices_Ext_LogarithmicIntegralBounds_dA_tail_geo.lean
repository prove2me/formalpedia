-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_tail_geo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:26.308797+00:00
-- url     : https://prove2.me/submissions/5a7be0b7-a754-436b-841b-9508027f1741

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
theorem _root_.solution (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (T M : ℕ) (hM : T ≤ M) :
    ∑ i ∈ Ioc T M, r ^ i + r ^ M ≤ r ^ T := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hTM ih =>
    rw [Finset.sum_Ioc_succ_top hTM, pow_succ]
    have hp : 0 ≤ r ^ M := pow_nonneg hr0 M
    have hq := mul_le_mul_of_nonneg_left hr hp
    linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
