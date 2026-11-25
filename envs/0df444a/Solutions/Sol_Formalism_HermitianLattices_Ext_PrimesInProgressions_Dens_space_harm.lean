-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.space_harm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:24:02.910817+00:00
-- url     : https://prove2.me/submissions/d2798479-e8f6-4e12-9efc-c5a447d1db95

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  · have h := harmonic_le_one_add_log x
    have e : ((harmonic x : ℚ) : ℝ) = ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; rfl
    rw [← e]; exact h
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
