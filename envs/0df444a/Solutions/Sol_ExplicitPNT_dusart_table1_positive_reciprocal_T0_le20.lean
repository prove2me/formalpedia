-- Prove2me | solution 1 for ExplicitPNT.dusart_table1_positive_reciprocal_T0_le20
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:36:08.420984+00:00
-- url     : https://prove2.me/submissions/981d790e-1c05-4e4c-ac91-978c7e9bd063

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_TaoFivePrimes_rh_verified_block_14_1e2
import Definitions.Def_dusart_psi_433_20261014_PsiZeroSum
import Definitions.Def_dusart_psi_433_20261014_PsiComparison
import Theorems.Thm_ExplicitPNT_DusartTable1_Modules_NumericalLowZeroReciprocal

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DusartSmoothing Complex
open ExplicitPNT.DusartTable1

theorem solution :
(∑' ρ : LowPositiveZero (566245491 / 500 : ℝ),
      (DusartSmoothing.RvM.zeroMult ρ.val : ℝ) * (1 / ρ.val.im)) ≤ 20 :=
  ExplicitPNT.DusartTable1.Modules.NumericalLowZeroReciprocal.2.2
