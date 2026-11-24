-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.WeightedSlopeBounds.Ga_bound5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:09.261896+00:00
-- url     : https://prove2.me/submissions/fe32e788-4b3d-4df4-9d98-961991903623

import Definitions.Def_Formalism_SizeWindowBrackets_QuotientSlopeBoundsWith
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_WeightedMeanData
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_UniformMeanTopLine
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_s_lower5
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_u_function_le_mean
import Theorems.Thm_Formalism_LFunctionChainParameters_WeightedSlopeBounds_key_identity5
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_Data_uF_nonneg
import Theorems.Thm_Formalism_RankGapBounds_WeightedMeanData_phi_bound


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
noncomputable section
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ)
namespace Formalism.LFunctionChainParameters.WeightedSlopeBounds
theorem _root_.solution (hS : D.HidaSetting C) (hDIV : D.DIV C) (hE : EComp5 D C)
    (hH : D.HComp C) (hCount : Count5 D C) (hSl : D.Slopes C) (hSN : QuotientSlopeBoundsWith D C Xpp)
    (hSI : D.SlopeIneq) (hHH : D.HHBound C) (hFP : D.FParams) (u0 : U0) :
    D.Ga u0 ≤ D.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + K0v5 D C
      + wmean (D.d u0) (Lo5 D C Xpp u0)
      + (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) := by
  have hsl := s_lower5 D C Xpp hS hDIV hE hCount hSl hSN u0
  have huF0 := D.uF_nonneg C hS u0
  have huF := u_function_le_mean D C Xpp hS hE hH hCount hSl hSN u0
  obtain ⟨hx, hb, -, -, -, hv, hf, -, hw, -, -, -, -, hdelBar, hetaBar, heBar0, heBar⟩ := hS
  have hid := key_identity5 D C hv hf u0 (hw u0)
  obtain ⟨hdel0, hdelle, heta0, hetale, he0, hele⟩ := hFP u0
  obtain ⟨hHH1, hHH2, hHH3⟩ := hHH u0
  have hSI' := hSI u0 hdel0 (by linarith) heta0 he0 (by linarith) hHH1 hHH2
  have hX : 0 < D.x ^ C.cHH := Real.rpow_pos_of_pos hx _
  have hphi := phi_bound huF0 hHH2 hHH3 hb hX huF
  have hA0 : 0 ≤ 4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0) :=
    mul_nonneg (by linarith)
      (Real.log_nonneg (by have := div_nonneg hHH2.le huF0; linarith))
  have hsq : Real.sqrt (D.e u0) ≤ Real.sqrt D.eBar := Real.sqrt_le_sqrt hele
  have hc0 : 0 ≤ D.η u0 + 4 * Real.sqrt (D.e u0) :=
    add_nonneg heta0 (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hc1 : 0 ≤ D.etaBar + 4 * Real.sqrt D.eBar :=
    add_nonneg hetaBar (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hB : (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
      ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
    calc (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0
        ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * D.HH u0 :=
          mul_le_mul_of_nonneg_right (by linarith) hHH2.le
      _ ≤ (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b) :=
          mul_le_mul_of_nonneg_left hHH3 hc1
  have hB0 : 0 ≤ (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0 := mul_nonneg hc0 hHH2.le
  have hinv : (1 - D.del u0)⁻¹ ≤ (1 - D.delBar)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hinv0 : 0 ≤ (1 - D.delBar)⁻¹ := inv_nonneg.mpr (by linarith)
  have hPhi : (1 - D.del u0)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
        + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0)
      ≤ (1 - D.delBar)⁻¹ * (4 * Real.log (1 + D.x ^ C.cHH)
          * (D.K3 C + wmean (D.d u0) (Lo5 D C Xpp u0) + D.b)
        + (D.etaBar + 4 * Real.sqrt D.eBar) * (D.x ^ C.cHH * D.b)) :=
    calc _ ≤ (1 - D.delBar)⁻¹ * (4 * D.uF u0 * Real.log (1 + D.HH u0 / D.uF u0)
          + (D.η u0 + 4 * Real.sqrt (D.e u0)) * D.HH u0) :=
          mul_le_mul_of_nonneg_right hinv (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hinv0
  unfold K0v5
  unfold K5v5 at hsl
  linarith
end Formalism.LFunctionChainParameters.WeightedSlopeBounds
