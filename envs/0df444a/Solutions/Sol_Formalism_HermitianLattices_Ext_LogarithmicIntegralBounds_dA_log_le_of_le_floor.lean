-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_log_le_of_le_floor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:12.408811+00:00
-- url     : https://prove2.me/submissions/1b2ec6fb-8c33-4051-aeaa-d6c2ad2625d0

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
theorem _root_.solution {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ ⌊x ^ 400⌋₊) :
    Real.log n ≤ 400 * Real.log x := by
  have h1 : (n:ℝ) ≤ x ^ 400 :=
    (Nat.cast_le.mpr hn).trans (Nat.floor_le (pow_nonneg (by linarith) 400))
  have h2 : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  calc Real.log n ≤ Real.log (x ^ 400) := Real.log_le_log h2 h1
    _ = 400 * Real.log x := by rw [Real.log_pow]; norm_num
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
