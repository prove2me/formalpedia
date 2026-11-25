-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.isExcPair_of_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:14.933996+00:00
-- url     : https://prove2.me/submissions/c8a39f5d-5d6b-4b5d-b0f4-3f30ae66c4b4

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_cZ_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_cZ_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_inRegion_ofReal
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_log_pos_of_two_le

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hr : InRegion cZ M (β : ℂ)) : IsExcPair χ β := by
  refine ⟨h2, h1, hz, ?_, ?_⟩
  · rw [inRegion_ofReal] at hr
    have hlogM := log_pos_of_two_le M hM
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
    have hcz := cZ_le
    have hcz0 := cZ_pos
    have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
    have h3 : cZ / Real.log ((M : ℝ) * 2) < 1 / (8 * Real.log M) := by
      rw [div_lt_div_iff₀ hlog2pos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hcz hlogM.le]
    linarith
  · by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (by simpa using hge) hz
end Formalism.HermitianLattices.Ext.PrimesInProgressions
