-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.hD_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:20.150949+00:00
-- url     : https://prove2.me/submissions/5b1a3893-41bd-4409-a4f4-99b021e6f786

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
theorem _root_.solution (φ : ℕ → ℂ) (x : ℂ) (b : ℕ) : hD φ x (b + 1) = x * hD φ x b + φ (b + 1) := by
  unfold hD
  rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_sum]
  congr 1
  refine sum_congr rfl (fun a ha => ?_)
  have : a ≤ b := Nat.lt_succ_iff.mp (mem_range.mp ha)
  rw [show b + 1 - a = (b - a) + 1 by omega, pow_succ]; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
