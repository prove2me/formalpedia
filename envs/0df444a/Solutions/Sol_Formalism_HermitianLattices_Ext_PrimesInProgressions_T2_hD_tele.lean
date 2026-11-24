-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.hD_tele
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:49.775788+00:00
-- url     : https://prove2.me/submissions/bd14c1fc-2164-4aa7-b905-600361e95254

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_hD_succ

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
theorem _root_.solution (φ : ℕ → ℂ) (x ζ : ℂ) (K : ℕ) :
    (1 - x * ζ) * ∑ b ∈ range (K + 1), hD φ x b * ζ ^ b =
      ∑ b ∈ range (K + 1), φ b * ζ ^ b - x * hD φ x K * ζ ^ (K + 1) := by
  induction K with
  | zero => simp [hD]; ring
  | succ K ih =>
    rw [sum_range_succ (fun b => hD φ x b * ζ ^ b) (K + 1), mul_add, ih,
      sum_range_succ (fun b => φ b * ζ ^ b) (K + 1), hD_succ]; ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.T2
