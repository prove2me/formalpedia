-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.weighted_mean_bound_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:23.636667+00:00
-- url     : https://prove2.me/submissions/8260da01-2d4d-43a9-9414-11fb604fe919

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_Ga_bound5
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_weighted_mean_lower_bound_le
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_umean_le_comb


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
    (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) : MeanBoundOfLossBounds D C Xpp := by
  intro hne hS hDIV hE hH hCount hSl hSN hLoss hSI hHH hFP
  have := hne
  have hx : 0 < D.x := hS.1
  have hdelBar : D.delBar < 1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcSl1 : 0 ≤ C.cSl1 := hS.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hLX : 0 ≤ Real.log (1 + D.x ^ C.cHH) := Real.log_nonneg (by linarith)
  have hc4 : 0 ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) :=
    mul_nonneg hinv0 (mul_nonneg (by norm_num) hLX)
  have hp : 0 ≤ (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1 :=
    mul_nonneg (by linarith) hcSl1
  have hGa : ∀ u0, D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ)
      + ((1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * C.cSl1) * D.IO u0
      + 0 * D.IO u0
      + (K0v5 D C + (1 + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH))) * K7v5 D C Xpp
        + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)) * (D.K3 C + D.b)
        + (1 - D.delBar)⁻¹ * ((D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b))) := by
    intro u0
    have h1 := Ga_bound5 D C Xpp hS hDIV hE hH hCount hSl hSN hSI hHH hFP u0
    have h2 := weighted_mean_lower_bound_le D C Xpp hS hCount u0
    have h3 := mul_le_mul_of_nonneg_left h2 hc4
    linarith
  have h1 := umean_le_comb (X := D.Ga) (A := D.Main)
    (B := fun u0 => Real.log (Fintype.card (W u0) : ℝ)) (P := D.IO) (E := D.IO) _ _ _ hGa
  have h2 := umean_le_comb (X := D.ASK) (A := fun u0 => D.ASK u0 - D.Ga u0) (B := D.Ga)
    (P := D.Ga) (E := D.Ga) 0 0 0 (fun i => by
      show D.ASK i ≤ (D.ASK i - D.Ga i) + D.Ga i + 0 * D.Ga i + 0 * D.Ga i + 0
      linarith)
  have h3 := mul_le_mul_of_nonneg_left hLoss.2 hp
  have h4 := hLoss.1
  unfold K0v5 Data.K3 K7v5 Data.EDiv at h1
  unfold errorTermWith UBar5 MLo5
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
