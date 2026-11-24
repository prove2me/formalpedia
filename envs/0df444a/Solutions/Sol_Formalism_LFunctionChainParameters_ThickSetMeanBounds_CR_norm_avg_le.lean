-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR.norm_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:54.519424+00:00
-- url     : https://prove2.me/submissions/f9d134db-ea5c-4d08-9db6-02f56d40662f

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_card_char
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_fPl_pos

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
theorem _root_.solution (S : Finset (E0 × H)) (hS : (S.card : ℝ) ≤ fPl H) (F : E0 × H → AddChar (E0 × H) ℂ → ℂ)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ g ∈ S, ∀ ψ, ‖F g ψ‖ ≤ K) :
    ‖(1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖
      ≤ 2 * fPl H * K := by
  have hf := fPl_pos (H := H)
  rw [norm_mul]
  have h1 : ‖(1 / ((PhiSet (H := H)).card : ℂ))‖ = 1 / fPl H := by
    unfold fPl; rw [norm_div, norm_one]; simp
  rw [h1]
  have h2 : ‖∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖ ≤ (S.card : ℝ) * (2 * fPl H) * K := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∀ g ∈ S, ‖∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖ ≤ (2 * fPl H) * K := by
      intro g hg
      refine le_trans (norm_sum_le _ _) ?_
      have : ∀ ψ ∈ (univ : Finset (AddChar (E0 × H) ℂ)), ‖ψ (-g) * F g ψ‖ ≤ K := by
        intro ψ _; rw [norm_mul, AddChar.norm_apply, one_mul]; exact hK g hg ψ
      refine le_trans (Finset.sum_le_sum this) ?_
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, card_char]
    refine le_trans (Finset.sum_le_sum this) ?_
    rw [Finset.sum_const, nsmul_eq_mul]; ring_nf; rfl
  calc 1 / fPl H * ‖∑ g ∈ S, ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * F g ψ‖
      ≤ 1 / fPl H * ((S.card : ℝ) * (2 * fPl H) * K) := by gcongr
    _ ≤ 1 / fPl H * (fPl H * (2 * fPl H) * K) := by
        gcongr
    _ = 2 * fPl H * K := by field_simp
end Formalism.LFunctionChainParameters.ThickSetMeanBounds.CR
