-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.mainPsi_sum_none
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:58:07.658073+00:00
-- url     : https://prove2.me/submissions/2a6eff6a-e400-42d9-a81f-ec71895741a5

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszAPOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (t β : ℝ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi none χ t = ((t - 0 * t ^ β / β : ℝ) : ℂ) := by
  have hu : IsUnit ((b : ZMod M)⁻¹) := by
    have h1 : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).mpr hb
    obtain ⟨u, hu⟩ := h1
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  simp only [mainPsi]
  simp [Finset.sum_ite_eq', MulChar.one_apply hu]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
