-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.signal_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:54.722673+00:00
-- url     : https://prove2.me/submissions/e2368386-d520-4d19-84d0-c4d810dad180

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_three_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) {x ε Cd CL y : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd)
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (hVal : ValuesAtX D ell x ε CL) :
    Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL
      ≤ (GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y).re := by
  have h0 : (GPsi D ell 0 y).re = Gz y := by simp [GPsi]
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hG := hDer.2 y x (by linarith) (by linarith)
  have hG' : |Gz y - Gz x| ≤ Cd := by
    calc |Gz y - Gz x| ≤ Cd * |y - x| := hG
      _ ≤ Cd * 1 := mul_le_mul_of_nonneg_left hy hCd
      _ = Cd := mul_one _
  have hGl := (abs_le.1 hG').1
  have b1 := three_bound D ell hx hCd hy hDer hVal psC (Or.inl rfl)
  have b2 := three_bound D ell hx hCd hy hDer hVal chC (Or.inr (Or.inl rfl))
  have b3 := three_bound D ell hx hCd hy hDer hVal chpsC (Or.inr (Or.inr rfl))
  have r1 := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) b1)).1
  have r2 := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) b2)).2
  have r3 := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) b3)).2
  simp only [Complex.add_re, Complex.sub_re, h0]
  unfold moveCost
  linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
