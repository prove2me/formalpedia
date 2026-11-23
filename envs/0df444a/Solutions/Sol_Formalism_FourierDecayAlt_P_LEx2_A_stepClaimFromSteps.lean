-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.stepClaimFromSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:36.828031+00:00
-- url     : https://prove2.me/submissions/7f1534f4-97d3-40eb-b73f-18ad1db7bd29

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A_ds_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution (hDs : DsMeas) : StepClaimFromSteps := by
  intro hCauchy hMarkovV hTF hTR hTS hTB hTL hCT hLeib hTZ hCI hAdj hEF hCS hSh hMk hTermB hGeom hES hAbs hUB hFat hDom
  intro B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp hInt Y hY
  have hImp' := hImp
  obtain ⟨hMeas, hWPos, hPReg, hI3, hAdjB, hJet, hI4, hI4', hI5a, hRes, hWR, hPR⟩ := hImp
  have hσ : (0:ℝ) ≤ σ := by linarith
  have hStar : S.Star σ := hAdj hCauchy hLeib hCT hCI hTS hTR B S c σ h4 hMeas hWPos hI3 hAdjB hJet hI4 hI4' hInt
  have hUni : Uniform B S σ CR Cd CP :=
    hUB hAdj hTermB hES hAbs hEF hSh hMk hCS hCI hTZ hGeom hTR hTS hTB hLeib hCT hCauchy hMarkovV
      B S c σ CR Cd CP h4 hCR hCd hCP hL hLbig hImp' hInt
  have hCoef : S.CoefInt σ := hCI B S σ hσ hMeas hWPos hI4 hI4'
  have hF : ∀ p : ℕ, Integrable (LE.sq B (S.d Y) (S.ds Y p)) B.μ := by
    intro p
    exact (hFat hTR hTL B (Bool × S.ι) (S.d Y) (S.ds Y p) σ _ hσ (fun ω a => (hWPos.2 Y hY ω a).le)
      (fun a => (hMeas.2.2 Y hY).1 a) (fun a => hDs B S hMeas hI4 Y hY p a)
      (fun ε hε => hCoef ε hε Y hY p) (fun ε hε => hUni ε hε Y hY p)).1
  refine ⟨?_, hDom hTR hTL hTB hTZ hCauchy B S σ h4 hMeas hWPos hI4 hStar hInt Y hY hF⟩
  have := hF 0
  rwa [ds_zero] at this
end Formalism.FourierDecayAlt.P.LEx2.A
