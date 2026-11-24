-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN.wG_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:30:46.416342+00:00
-- url     : https://prove2.me/submissions/dd02089d-113d-455c-ac9b-2d37f95d5220

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_AN_truncC

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
open Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ≠ 0)
    (A w : ℝ) (hw : 0 < w) (M : ℕ) (hM : ⌊A / w⌋₊ ≤ M) :
    (w : ℂ) * GPsi D ell ψ (A / w)
      = ∑ n ∈ Icc 1 M, (Λ n : ℂ) * primVal D ψ n * ((max (A / n - w) 0 : ℝ) : ℂ) + (A : ℂ) * ell ψ := by
  have t := truncC (fun n => (Λ n : ℂ) * primVal D ψ n) (A / w) M hM
  unfold GPsi
  rw [if_neg hψ, t, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast hn.1
      exact this.ne'
    have : max (A / n - w) 0 = w * max (A / w / n - 1) 0 := by
      rw [mul_max_of_nonneg _ _ hw.le, mul_zero]
      congr 1
      field_simp
    rw [this]; push_cast; ring
  · rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ hw.ne']
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.AN
