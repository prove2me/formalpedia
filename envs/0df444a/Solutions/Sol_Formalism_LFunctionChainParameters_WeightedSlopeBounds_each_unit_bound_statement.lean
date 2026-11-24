-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.each_unit_bound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:03:30.436596+00:00
-- url     : https://prove2.me/submissions/273b584d-6229-43a7-952d-74f8798ca045

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_Ga_bound5
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_weighted_mean_lower_bound_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.WeightedSlopeBounds
open Formalism.RankGapBounds.WeightedMeanData
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
theorem _root_.solution {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : PointwiseBoundVariant D C Xpp := by
  intro hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP u0
  have hx : 0 < D.x := hS.1
  have hdelBar : D.delBar < 1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcSl1 : 0 ≤ C.cSl1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) :=
    mul_nonneg hinv0 (mul_nonneg (by norm_num) hLX)
  have h1 := Ga_bound5 D C Xpp hS hDIV hE hH hCount hSl hSN hSI hHH hFP u0
  have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
  have hIO := mul_le_mul_of_nonneg_left (hLoss u0).2 hcSl1
  have hML : wmean (D.d u0) (Lo5 D C Xpp u0) ≤ MLo5 D C Xpp := by
    unfold MLo5; unfold K7v5 at h2; linarith
  have h3 := mul_le_mul_of_nonneg_left hML hc4
  have h4 := (hLoss u0).1
  unfold Data.K3 at h1
  unfold K0v5 Data.EDiv at h1
  unfold ErrX5at UBar5
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
