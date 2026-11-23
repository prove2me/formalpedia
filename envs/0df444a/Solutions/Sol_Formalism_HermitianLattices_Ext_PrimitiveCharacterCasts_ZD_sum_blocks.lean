-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:03.249831+00:00
-- url     : https://prove2.me/submissions/e76ca1a4-ab6a-48f3-9d40-2a087334f475

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDetect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
open scoped ArithmeticFunction.Moebius
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution (f : ℕ → ℂ) (Y : ℕ) : ∀ J : ℕ,
    ∑ n ∈ Ioc Y (Y * 2 ^ J), f n = ∑ j ∈ range J, ∑ n ∈ Ioc (Y * 2 ^ j) (2 * (Y * 2 ^ j)), f n
  | 0 => by simp
  | J + 1 => by
    rw [sum_range_succ, ← solution f Y J]
    have h1 : Y ≤ Y * 2 ^ J := Nat.le_mul_of_pos_right Y (by positivity)
    have h2 : Y * 2 ^ J ≤ Y * 2 ^ (J + 1) := Nat.mul_le_mul_left Y (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show 2 * (Y * 2 ^ J) = Y * 2 ^ (J + 1) by ring]
    exact (Finset.sum_Ioc_consecutive _ h1 h2).symm
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
