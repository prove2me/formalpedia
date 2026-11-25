-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.etaOf_far
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:40.937209+00:00
-- url     : https://prove2.me/submissions/2a58bed9-8433-44c8-bce5-db46a2b319f7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_cZ_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_cZ_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_inRegion_ofReal
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_log_two_mul_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_log_pos_of_two_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_etaOf_some

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
theorem _root_.solution (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ)
    (h : eOf M = some (χ₁, β₁)) (hr : ¬ InRegion cZ M (β₁ : ℂ)) : cZ / 2 ≤ etaOf M := by
  rw [etaOf_some M χ₁ β₁ h]
  rw [inRegion_ofReal] at hr
  push_neg at hr
  have hlogM := log_pos_of_two_le M hM
  have hlog2 := log_two_mul_le M hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
  have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
  have hcz := cZ_le
  have hcz0 := cZ_pos
  have h1 : cZ / Real.log ((M : ℝ) * 2) < 1 - β₁ := by linarith
  have hb : 0 < 1 - β₁ := lt_trans (div_pos hcz0 hlog2pos) h1
  rw [div_lt_iff₀ hlog2pos] at h1
  have h2 : cZ / 2 ≤ (1 - β₁) * Real.log M := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hb.le]
  exact le_min (by linarith) h2
end Formalism.HermitianLattices.Ext.PrimesInProgressions
