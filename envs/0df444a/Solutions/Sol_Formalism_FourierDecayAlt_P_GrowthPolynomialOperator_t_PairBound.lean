-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PairBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:58.806277+00:00
-- url     : https://prove2.me/submissions/7288bdcd-3aea-4676-8f41-45c39dabbdef

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : PairBound := by
  intro hPBA hPI hEI hPS hSF hNP hNE hND hNL hNN hNGE hEZ τ Rw I H H₁ _ _ _ _ _ _ X k r f b g1 g2 c Cn
    δ e1 dd hSN hdd hδ0 hδ he0 he1 hAC hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG
  obtain ⟨hb, hk32, hfk, hr, hg1, hg2, hlb, hc, hCn⟩ := hSN
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hk1 : 1 ≤ k := by omega
  obtain ⟨-, -, hPg0, hPg⟩ := hNP f k b g1 g2 hb1 hk1 hfk hg1 hg2
  have hE := hNE k b (by linarith) hlb
  obtain ⟨hD1, hD2⟩ := hND k r f hfk hk32 hr
  have hL := hNL k f c hc
  have hG := hNGE k r (by omega)
  have hN := hNN k (2 * r + 2) f Cn b hCn
  have hε' : ((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ *
      Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b) ≤ (b ^ 14)⁻¹ :=
    (mul_le_mul_of_nonneg_right hG (Real.exp_pos _).le).trans (hN.trans hE)
  have he1' : e1 ≤ Real.exp ((b ^ 14)⁻¹) :=
    he1.trans (Real.exp_le_exp.mpr ((hD1.trans hD2).trans hE))
  have hb7 : (0:ℝ) ≤ (b ^ 7)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) 7)
  have hA : (1 + δ) * e1 ≤ (1 + (b ^ 7)⁻¹) * Real.exp ((b ^ 14)⁻¹) :=
    mul_le_mul (by linarith) he1' he0 (by linarith)
  have hmain := hPBA hPI hEI hPS hSF τ Rw I H H₁ X ((1 + 3 / g1) ^ f * (1 + 3 / g2) ^ f)
    ((1 + δ) * e1) (Real.exp (-(c * k * f * Real.log k)))
    (((2 : ℝ) ^ (k - 2 * r - 5))⁻¹ * Real.exp (Cn * ((2 * r + 2 : ℕ) : ℝ) ^ 5 * f * Real.log b)) dd
    hPg0 hdd hAC hNX hGG hRO hCP hIZ hRB hRNS hRM hRNG
  have hfin := hEZ b _ _ _ _ hb hPg0 hPg hA (hL.trans hE) hε'
  exact hmain.trans (mul_le_mul_of_nonneg_right hfin hdd)
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
