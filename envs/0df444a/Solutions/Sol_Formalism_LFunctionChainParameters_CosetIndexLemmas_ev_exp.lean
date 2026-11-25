-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.CosetIndexLemmas.ev_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:46:13.044312+00:00
-- url     : https://prove2.me/submissions/811e642b-204f-4aa9-8c10-d789a99db81e

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBracketBoundOfSizeWindows
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.CosetIndexLemmas
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost
open Filter Asymptotics
namespace Formalism.LFunctionChainParameters.CosetIndexLemmas
theorem _root_.solution (A B κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x, x₀ ≤ x → A * x ^ B ≤ Real.exp (κ * x ^ δ) := by
  have hc : 0 < κ / (2 * (|B| + 1)) := by positivity
  have hb := (isLittleO_log_rpow_atTop hδ).bound hc
  have h2 := (tendsto_rpow_atTop hδ).eventually_ge_atTop (2 * |A| / κ)
  obtain ⟨x₀, hx₀⟩ := (hb.and h2).exists_forall_of_atTop
  refine ⟨max x₀ 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₀ x (le_trans (le_max_left _ _) hx)
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  have hxd : 0 ≤ x ^ δ := Real.rpow_nonneg hx0.le _
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0, abs_of_nonneg hxd] at h1
  have hA : |A| ≤ κ * x ^ δ / 2 := by
    rw [div_le_iff₀ hκ] at h2; linarith
  have hB : B * Real.log x ≤ κ * x ^ δ / 2 := by
    have hB1 : B * Real.log x ≤ |B| * Real.log x := mul_le_mul_of_nonneg_right (le_abs_self B) hl0
    have hB2 : |B| * Real.log x ≤ (|B| + 1) * (κ / (2 * (|B| + 1)) * x ^ δ) := by
      apply mul_le_mul (by linarith) h1 hl0 (by positivity)
    have hB3 : (|B| + 1) * (κ / (2 * (|B| + 1)) * x ^ δ) = κ * x ^ δ / 2 := by
      field_simp
    linarith
  have hxB : x ^ B = Real.exp (B * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  have hxB0 : 0 < x ^ B := Real.rpow_pos_of_pos hx0 _
  calc A * x ^ B ≤ |A| * x ^ B := mul_le_mul_of_nonneg_right (le_abs_self A) hxB0.le
    _ ≤ Real.exp |A| * x ^ B := by
        apply mul_le_mul_of_nonneg_right _ hxB0.le
        have := Real.add_one_le_exp |A|; linarith
    _ = Real.exp (|A| + B * Real.log x) := by rw [hxB, Real.exp_add]
    _ ≤ Real.exp (κ * x ^ δ) := Real.exp_le_exp.2 (by linarith)
end Formalism.LFunctionChainParameters.CosetIndexLemmas
