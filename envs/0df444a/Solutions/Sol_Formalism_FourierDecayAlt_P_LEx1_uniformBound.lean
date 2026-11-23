-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.uniformBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:14.255915+00:00
-- url     : https://prove2.me/submissions/5749aa18-37a5-447d-98c1-263989625320

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : UniformBound := by
  intro hAdj hTermB hES hAbs hEF hSh hMk hCS hCI hTZ hGeom hTR hTS hTB hLeib hCT hCauchy hMarkovV
  intro B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp hInt ε hε Y hY p
  have hImp' := hImp
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hStar : S.Star σ := hAdj hCauchy hLeib hCT hCI hTS hTR B S c σ h4 hMeas hWPos hI3 hAdjB hJet hI4 hI4' hInt
  have hb := hEF B S σ ε hε hPReg hI4'
  have hT := hTermB hCS hSh hMk hCI hEF hTB hCauchy hMarkovV B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hImp'
  have hE := hES hTZ hGeom hTR B S c σ ε CR Cd CP h4 hε hCR hCd hCP hL hLbig hImp' hInt hStar hT
  have hA := hAbs B S σ ε S.A0 hL.le hb hE
  have h2 := hSh B S σ ε CR Cd CP hσ hε hCR hCd hCP hMeas hWPos hPReg hI4' hI5a hRes hWR hPR hb
  have h3 := hMk hMarkovV B S σ ε (C7 CR Cd CP * S.Esup ε σ * |S.P Y|) hσ hε hL hMeas hWPos hI4 hI4' Y hY
    (fun s hs => h2 Y s hY hs) p
  have hC7 : 0 ≤ C7 CR Cd CP := by unfold C7; positivity
  refine le_trans h3 ?_
  have hm : 0 ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) := by positivity
  have : C7 CR Cd CP * S.Esup ε σ * |S.P Y| ≤ C7 CR Cd CP * (2 * S.A0) * |S.P Y| := by
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left hA hC7
  calc _ ≤ (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) * (C7 CR Cd CP * (2 * S.A0) * |S.P Y|) :=
        mul_le_mul_of_nonneg_left this hm
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.LEx1
