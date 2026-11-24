-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.three_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:48:04.050738+00:00
-- url     : https://prove2.me/submissions/f1d01c40-0681-40d2-9cfa-4c50349aa5f8

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_psC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_chpsC_ne_zero
import Theorems.Thm_Formalism_D5_Bal_chC_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_PB_chC_ne_zero


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
    (hy : |y - x| ≤ 1) (hDer : DerivInt D ell Cd) (hVal : ValuesAtX D ell x ε CL)
    (ψ : AddChar (E0 × H) ℂ) (hψ : ψ = psC ∨ ψ = chC ∨ ψ = chpsC) :
    ‖GPsi D ell ψ y‖ ≤ x ^ ((1 : ℝ) / 2 + ε) + (Real.log (x + 1) + Cd + CL * Real.log x) := by
  have hψ0 : ψ ≠ 0 := by
    rcases hψ with rfl | rfl | rfl
    · exact psC_ne_zero
    · exact chC_ne_zero
    · exact chpsC_ne_zero
  obtain ⟨hv, hl⟩ := hVal ψ hψ
  obtain ⟨hy1, hy2⟩ := abs_le.1 hy
  have hd := hDer.1 ψ hψ0 y x (by linarith) (by linarith)
  have hmax : max y x ≤ x + 1 := max_le (by linarith) (by linarith)
  have hmax1 : 1 ≤ max y x := le_trans (by linarith) (le_max_right y x)
  have hlog : Real.log (max y x) ≤ Real.log (x + 1) := Real.log_le_log (by linarith) hmax
  have hlog0 : 0 ≤ Real.log (max y x) := Real.log_nonneg hmax1
  have hs : 0 ≤ Real.log (max y x) + Cd + ‖ell ψ‖ := by positivity
  have h1 : |y - x| * (Real.log (max y x) + Cd + ‖ell ψ‖) ≤ Real.log (max y x) + Cd + ‖ell ψ‖ := by
    calc |y - x| * (Real.log (max y x) + Cd + ‖ell ψ‖) ≤ 1 * (Real.log (max y x) + Cd + ‖ell ψ‖) :=
          mul_le_mul_of_nonneg_right hy hs
      _ = _ := one_mul _
  have h2 : ‖GPsi D ell ψ y‖ ≤ ‖GPsi D ell ψ x‖ + ‖GPsi D ell ψ y - GPsi D ell ψ x‖ := by
    have := norm_add_le (GPsi D ell ψ x) (GPsi D ell ψ y - GPsi D ell ψ x)
    simpa using this
  linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
