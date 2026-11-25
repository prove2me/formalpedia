-- Prove2me | solution 1 for Formalism.L2.LamCM.detLineMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:09:27.435713+00:00
-- url     : https://prove2.me/submissions/d56a0e44-7dc5-4933-b6e9-9af1596fb413

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal
import Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_pos__7ef009ed3ead
import Theorems.Thm_P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_isFractional
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_coe
import Theorems.Thm_Formalism_L2_LamCM_A2_detIdeal_ne_zero
import Theorems.Thm_Formalism_L2_LamCM_A2_deg_detLine
import Theorems.Thm_Formalism_L2_LamCM_A2_detSub_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open A2
namespace Formalism.L2.LamCM
theorem _root_.solution : DetMono := by
  intro K _ _ m L L' hL hL' hH hM
  have hf := detSub_isFractional L hL.1
  have hf' := detSub_isFractional L' hL'.1
  have hle : L'.detIdeal ≤ L.detIdeal := by
    rw [← FractionalIdeal.coe_le_coe, detIdeal_coe L hf, detIdeal_coe L' hf']
    exact detSub_mono hM
  have hN := absNorm_anti' hle (detIdeal_ne_zero L' hL')
  have hpos := absNorm_pos' (detIdeal_ne_zero L hL)
  rw [deg_detLine, deg_detLine, hH]
  have : Real.log ((FractionalIdeal.absNorm L.detIdeal : ℚ) : ℝ) ≤
      Real.log ((FractionalIdeal.absNorm L'.detIdeal : ℚ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hN)
  linarith
end Formalism.L2.LamCM
