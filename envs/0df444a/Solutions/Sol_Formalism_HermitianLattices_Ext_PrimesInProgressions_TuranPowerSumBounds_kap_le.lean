-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.kap_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:53.100572+00:00
-- url     : https://prove2.me/submissions/fcded570-c077-4426-9486-34c0749d27ad

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TwentyFiveMulSmallConstant
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_th_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_eps_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_eps_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_TuranPowerSumBounds_kap_pos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : kap a D ≤ th a := by
  have hh := th_pos a
  have hi := eps_pos a
  have hi16 := eps_le a
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hM : (1 : ℝ) ≤ a * (D + 1) := by nlinarith
  have hMne : (a : ℝ) * (D + 1) ≠ 0 := (lt_of_lt_of_le one_pos hM).ne'
  have hs : kap a D * ((a : ℝ) * (D + 1)) = th a * eps a ^ 2 := by
    unfold kap
    exact div_mul_cancel_of_ne_zero_real _ _ hMne
  have hs0 : 0 ≤ kap a D := (kap_pos a ha D hD).le
  have hi2 : eps a ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul hi16 hi16 hi.le (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hhi := mul_le_mul_of_nonneg_left hi2 hh.le
  have hsM := mul_le_mul_of_nonneg_left hM hs0
  nlinarith [hs, hhi, hsM]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
