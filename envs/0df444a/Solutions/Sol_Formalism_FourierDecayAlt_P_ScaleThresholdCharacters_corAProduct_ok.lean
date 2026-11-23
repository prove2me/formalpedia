-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScaleThresholdCharacters.corAProduct_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:40.916803+00:00
-- url     : https://prove2.me/submissions/8d3d12d1-fe30-460e-b4d4-7801e98e1055

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScaleThresholdCharacters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
theorem _root_.solution : CorAProduct := by
  intro n TT IL y q x P QQ hTT hIL hn hq hqpos hx hP hPr
  have hb : 0 < |P (y + 1)| := abs_pos.mpr hP
  have ha : 0 ≤ |P y| := abs_nonneg _
  have hQ0 : 0 ≤ |QQ (y + 1 / 2)| := abs_nonneg _
  have hexp : Real.exp (4 * n / IL) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by rw [div_le_one hIL]; exact hn)
  have hab : |P y| ≤ Real.exp 1 * |P (y + 1)| := by
    have h1 : |P y| / |P (y + 1)| ≤ Real.exp 1 := by rw [← abs_div]; exact hPr.trans hexp
    rwa [div_le_iff₀ hb] at h1
  have hxa : 0 ≤ |x (y + 1)| := abs_nonneg _
  have hxa2 : |x (y + 1)| ^ 2 ≤ |QQ (y + 1 / 2)| := by
    have := pow_le_pow_left₀ hxa hx 2
    rwa [Real.sq_sqrt hQ0] at this
  have hs0 : 0 ≤ TT ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hTT.le _
  have hs2 : (TT ^ (-(1 / 2 : ℝ))) ^ 2 = TT⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTT.le]
    norm_num
    exact Real.rpow_neg_one TT
  have hu2 : Real.sqrt (|P y * P (y + 1)| / q y) ^ 2 = |P y| * |P (y + 1)| / q y := by
    rw [Real.sq_sqrt (by positivity), abs_mul]
  have he2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  rw [abs_mul]
  have hLn : 0 ≤ |x (y + 1)| * |P y| / q y := by positivity
  have hRn : 0 ≤ Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hQv : |QQ (y + 1 / 2)| = q y / TT := by rw [hq]; field_simp
  have hsq : (|x (y + 1)| * |P y| / q y) ^ 2 ≤
      (Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have e1 : (|x (y + 1)| * |P y| / q y) ^ 2 = |x (y + 1)| ^ 2 * |P y| ^ 2 / q y ^ 2 := by ring
    have e2 : (Real.exp (1 / 2) * Real.sqrt (|P y * P (y + 1)| / q y) * TT ^ (-(1 / 2 : ℝ))) ^ 2 =
        Real.exp (1 / 2) ^ 2 * Real.sqrt (|P y * P (y + 1)| / q y) ^ 2 * (TT ^ (-(1 / 2 : ℝ))) ^ 2 := by
      ring
    rw [e1, e2, hu2, hs2, he2]
    calc |x (y + 1)| ^ 2 * |P y| ^ 2 / q y ^ 2 ≤ |QQ (y + 1 / 2)| * |P y| ^ 2 / q y ^ 2 := by gcongr
      _ = |P y| ^ 2 / (TT * q y) := by rw [hQv]; field_simp
      _ ≤ Real.exp 1 * |P (y + 1)| * |P y| / (TT * q y) := by gcongr; nlinarith
      _ = Real.exp 1 * (|P y| * |P (y + 1)| / q y) * TT⁻¹ := by field_simp
  nlinarith
end Formalism.FourierDecayAlt.P.ScaleThresholdCharacters
